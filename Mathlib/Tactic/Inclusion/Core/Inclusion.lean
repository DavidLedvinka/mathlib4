module

public import Mathlib.Tactic.Inclusion.Core.Prod
public import Lean.Compiler.IR.CompilerM
public meta import Lean.Elab.Term.TermElabM

set_option linter.style.header false

@[expose] public section

open Lean Meta Elab Term

namespace IntervalArithmetic

initialize registerTraceClass `Tactic.inclusion

structure ExprInclusionFunction where
  ivars : Array Expr
  iVarTypes : Array IVarType
  outputType : IVarType
  /- `f : α₁ → ... → αₙ → β` such that `f ivars = e` -/
  expr : Expr
  /- `F : Iα₁ → ... → Iαₙ → Iβ` -/
  inclusion : Expr
  /- The curried containment proof for `F` and `f`. -/
  proof : Expr

def ExprInclusionFunction.uncurry (fn : ExprInclusionFunction) :
    MetaM UncurriedInclusion := do
  let result ← uncurryInclusion fn.iVarTypes fn.expr fn.inclusion fn.proof
  let expectedProofType ← mkAppOptM ``IsInclusionFunction
    #[result.iVarType.setType, result.iVarType.exprType, fn.outputType.setType,
      fn.outputType.exprType, result.iVarType.toSetInst, fn.outputType.toSetInst,
      result.inclusion, result.expr]
  unless ← isDefEq (← inferType result.proof) expectedProofType do
    throwError "Inclusion extension returned a proof with an unexpected type"
  return result

structure ExprInclusionBody where
  inclusionBody : Expr
  proofBody : Expr

def IVarData.toExprInclusionBody (data : IVarData) : ExprInclusionBody :=
  ⟨data.setVar, data.hypVar⟩

structure InclusionM.Context where
  localContext : LocalContext
  localInstances : LocalInstances

structure InclusionM.State where
  ivars : ExprMap IVarData := {}

abbrev InclusionM := ReaderT InclusionM.Context <| StateT InclusionM.State MetaM

instance : MonadBacktrack (Meta.SavedState × InclusionM.State) InclusionM where
  saveState := do return ⟨← Meta.saveState, ← get⟩
  restoreState s := do
    s.1.restore
    set s.2

def InclusionM.run {α : Type} (x : InclusionM α) : MetaM α := do
  let localContext ← getLCtx
  let localInstances ← getLocalInstances
  StateT.run' (ReaderT.run x { localContext, localInstances }) {}

def mkIVar (e setType toSetInst : Expr) : InclusionM IVarData := do
  let ctx ← read
  unless ← MetavarContext.isWellFormed ctx.localContext e do
    throwError "Cannot create an inclusion variable for {e} because it depends on variables \
      introduced while constructing the inclusion function"
  let eType ← inferType e
  unless ← MetavarContext.isWellFormed ctx.localContext eType do
    throwError "Cannot create an inclusion variable for {e} because its type depends on variables \
      introduced while constructing the inclusion function"
  unless ← MetavarContext.isWellFormed ctx.localContext setType do
    throwError "Cannot use set type {setType} for {e} because it depends on variables introduced \
      while constructing the inclusion function"
  unless ← MetavarContext.isWellFormed ctx.localContext toSetInst do
    throwError "Cannot use the `ToSet` instance for {e} because it depends on variables introduced \
      while constructing the inclusion function"
  let exprVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances eType .syntheticOpaque
  let setVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances setType .syntheticOpaque
  let hypType ← mkToSetMem eType setType exprVar setVar toSetInst
  let hypVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances hypType .syntheticOpaque
  let data := ⟨⟨eType, setType, toSetInst⟩, exprVar, setVar, hypVar⟩
  modify fun state => { state with ivars := state.ivars.insert e data }
  return data

def mkExprInclusionFunction (e : Expr) (body : ExprInclusionBody) :
    InclusionM ExprInclusionFunction := do
  let state ← get
  let (ivars, iVarDatas) := state.ivars.toArray.unzip
  let exprVars := iVarDatas.map (·.exprVar)
  let setVars := iVarDatas.map (·.setVar)
  let hypVars := iVarDatas.map (·.hypVar)
  let iVarTypes := iVarDatas.map (·.iVarType)
  let exprBody := e.replace fun subterm => state.ivars[subterm]?.map (·.exprVar)
  let bodyProofType ← inferType body.proofBody
  let some (outputExpr, outputSet, outputToSetInst) := toSetHyp? bodyProofType
    | throwError "Inclusion extension returned a proof of {bodyProofType}, expected a containment \
        proof using a `ToSet` instance"
  unless ← isDefEq outputExpr exprBody do
    throwError "Inclusion extension returned a proof for an unexpected expression"
  unless ← isDefEq outputSet body.inclusionBody do
    throwError "Inclusion extension returned a proof for an unexpected inclusion"
  let outputType : IVarType :=
    ⟨← inferType outputExpr, ← inferType outputSet, outputToSetInst⟩
  let curriedExpr ← mkLambdaFVars exprVars exprBody (binderInfoForMVars := .default)
  let curriedInclusion ← mkLambdaFVars setVars body.inclusionBody (binderInfoForMVars := .default)
  let curriedProof ← mkLambdaFVars (exprVars ++ setVars ++ hypVars) body.proofBody
    (binderInfoForMVars := .default)
  return ⟨ivars, iVarTypes, outputType, curriedExpr, curriedInclusion, curriedProof⟩

structure InclusionExt where
  name : Name := by exact decl_name%
  eval (e : Expr) : InclusionM ExprInclusionBody
  priority : Nat := eval_prio default

def mkInclusionExt (n : Name) : ImportM InclusionExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck InclusionExt opts ``InclusionExt n

abbrev InclusionExtEntry := Array (Array DiscrTree.Key) × Name

structure InclusionExts where
  tree : DiscrTree InclusionExt := {}
  erased : PHashSet Name := {}
  deriving Inhabited

def InclusionExts.eraseCore (exts : InclusionExts) (declName : Name) : InclusionExts :=
  { exts with erased := exts.erased.insert declName }

def InclusionExts.erase {m : Type → Type} [Monad m] [MonadError m]
    (exts : InclusionExts) (declName : Name) : m InclusionExts := do
  unless exts.tree.values.any (·.name == declName) && !exts.erased.contains declName do
    throwError "'{declName}' does not have [inclusionExt] attribute"
  return exts.eraseCore declName

initialize inclusionExt :
    ScopedEnvExtension InclusionExtEntry (InclusionExtEntry × InclusionExt) InclusionExts ←
  have : BEq InclusionExt := ⟨fun _ _ ↦ false⟩
  let insert kss v dt := kss.foldl (fun dt ks ↦ dt.insertKeyValue ks v) dt
  registerScopedEnvExtension {
    mkInitial := pure {}
    ofOLeanEntry := fun _ e@(_, n) ↦ return (e, ← mkInclusionExt n)
    toOLeanEntry := (·.1)
    addEntry := fun { tree, erased } ((kss, n), ext) ↦
      { tree := insert kss ext tree, erased := erased.erase n }
  }

syntax (name := inclusionExtAttr) "inclusionExt" term,+ : attr

/-- The `inclusionExt` attribute registers an inclusion-function extension. -/
initialize registerBuiltinAttribute {
  name := `inclusionExtAttr
  descr := "adds an inclusion-function extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| inclusionExt $es,*) => do
      let env ← getEnv
      ensureAttrDeclIsMeta `inclusionExt declName kind
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute `inclusionExt`, declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return
      let ext ← mkInclusionExt declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx ↦ do
        let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
      inclusionExt.add ((keys, declName), ext) kind
    | _ => throwUnsupportedSyntax
  erase := fun declName => do
    let s := inclusionExt.getState (← getEnv)
    let s ← s.erase declName
    modifyEnv fun env => inclusionExt.modifyState env fun _ => s
}

def mkExprInclusionBody (e : Expr) : InclusionM ExprInclusionBody := do
  if let some data := (← get).ivars[e]? then
    trace[Tactic.inclusion] "Reusing ivar for {e}"
    return data.toExprInclusionBody
  let s ← saveState
  let inclusionExts := inclusionExt.getState (← getEnv)
  let exts ← inclusionExts.tree.getMatch e
  let exts := exts.qsort (fun ext₁ ext₂ ↦ ext₁.priority < ext₂.priority)
  for ext in exts do
    if !inclusionExts.erased.contains ext.name then
      try
        let body ← ext.eval e
        recordExtraModUseFromDecl (isMeta := true) ext.name
        trace[Tactic.inclusion] "{ext.name} applied to {e}"
        return body
      catch err =>
        trace[Tactic.inclusion] "Failed to apply {ext.name} to {e} : {err.toMessageData}"
        restoreState s
  throwError "No inclusion extension applies to {e}"

def toExprInclusionFunction (e : Expr) : MetaM ExprInclusionFunction :=
  InclusionM.run do
    let body ← mkExprInclusionBody e
    mkExprInclusionFunction e body

end IntervalArithmetic
