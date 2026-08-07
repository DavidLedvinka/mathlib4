module

public meta import Mathlib.Tactic.Inclusion.Core.Expr
public import Lean.Compiler.IR.CompilerM
public meta import Lean.Elab.Term.TermElabM

set_option linter.style.header false

public meta section

open Lean Meta Elab Term

namespace Inclusion

initialize registerTraceClass `Tactic.inclusion

structure InclusionParamDecl where
  name : Name
  enabledByDefault : Bool := false
  defaultValue : Nat := 0

structure InclusionParams where
  decls : Array InclusionParamDecl := #[]
  deriving Inhabited

def mkInclusionParamDecl (n : Name) : ImportM InclusionParamDecl := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck InclusionParamDecl opts ``InclusionParamDecl n

initialize inclusionParamExt :
    ScopedEnvExtension Name (Name × InclusionParamDecl) InclusionParams ←
  registerScopedEnvExtension {
    mkInitial := pure {}
    ofOLeanEntry := fun _ n => return (n, ← mkInclusionParamDecl n)
    toOLeanEntry := (·.1)
    addEntry := fun state (_, decl) => { state with decls := state.decls.push decl }
  }

syntax (name := inclusionParamAttr) "inclusionParam" : attr

/-- The `inclusionParam` attribute registers a named natural-number inclusion parameter. -/
initialize registerBuiltinAttribute {
  name := `inclusionParamAttr
  descr := "registers an inclusion-tactic parameter"
  applicationTime := .afterCompilation
  add := fun declName _ kind => do
    let env ← getEnv
    ensureAttrDeclIsMeta `inclusionParam declName kind
    unless (env.getModuleIdxFor? declName).isNone do
      throwError "invalid attribute `inclusionParam`, declaration is in an imported module"
    if (IR.getSorryDep env declName).isSome then return
    let decl ← mkInclusionParamDecl declName
    let params := inclusionParamExt.getState env
    if params.decls.any fun existing => existing.name == decl.name then
      throwError "Inclusion parameter '{decl.name}' is already registered"
    inclusionParamExt.add (declName, decl) kind
}

def InclusionParams.find? (params : InclusionParams) (name : Name) : Option InclusionParamDecl :=
  params.decls.find? fun decl => decl.name == name

def mergeInclusionParams (params more : Array Name) : Array Name :=
  more.foldl (fun params name => if params.contains name then params else params.push name) params

def inclusionParamArgs (params : Array Name) (paramVars : Array Expr)
    (wanted : Array Name) : MetaM (Array Expr) :=
  wanted.mapM fun name => do
    let some i := params.findIdx? (· == name)
      | throwError "Internal error: inclusion parameter '{name}' was not abstracted"
    return paramVars[i]!

def withInclusionParams {α : Type} (params : Array Name)
    (k : Array Expr → MetaM α) : MetaM α := do
  let some result ← withLocalDeclsD
      (params.map fun name => (name, fun _ => pure (mkConst ``Nat))) fun paramVars =>
        some <$> k paramVars
    | throwError "Internal error while introducing inclusion parameters"
  return result

/-- Close an inclusion function by substituting a closed inclusion function for every inclusion
variable. Parameter names are merged, so all computations remain reusable while their concrete
natural-number values are chosen later. -/
def ExprInclusionFunction.closeWithBounds (fn : ExprInclusionFunction)
    (bounds : Array ExprInclusionFunction) : MetaM ExprInclusionFunction := do
  unless fn.iexprs.size = bounds.size do
    throwError "Internal error: the inclusion function and its bounds have different lengths"
  if fn.iexprs.isEmpty then
    return fn
  let mut params := fn.params
  for bound in bounds do
    unless bound.iexprs.isEmpty do
      throwError "A hypothesis bound depends on an unbounded inclusion variable"
    params := mergeInclusionParams params bound.params
  withInclusionParams params fun paramVars => do
    let fnParamArgs ← inclusionParamArgs params paramVars fn.params
    let inclusionFn := (mkAppN fn.inclusion fnParamArgs).headBeta
    let proofFn := (mkAppN fn.proof fnParamArgs).headBeta
    let mut sets := Array.mkEmpty bounds.size
    let mut hyps := Array.mkEmpty bounds.size
    for h : i in [:bounds.size] do
      let bound := bounds[i]
      let some expected := fn.iexprs[i]?
        | throwError "Internal error: missing inclusion variable"
      let expectedType := expected.iVarType
      unless ← isDefEq bound.outputType.elemType expectedType.elemType do
        throwError "A hypothesis bound has expression type {bound.outputType.elemType}, expected \
          {expectedType.elemType}"
      unless ← isDefEq bound.outputType.setType expectedType.setType do
        throwError "A hypothesis bound has set type {bound.outputType.setType}, expected \
          {expectedType.setType}"
      unless ← isDefEq bound.outputType.toSetInst expectedType.toSetInst do
        throwError "A hypothesis bound uses an unexpected `ToSet` instance"
      let boundParamArgs ← inclusionParamArgs params paramVars bound.params
      sets := sets.push ((mkAppN bound.inclusion boundParamArgs).headBeta)
      hyps := hyps.push ((mkAppN bound.proof boundParamArgs).headBeta)
    let inclusionBody := mkAppN inclusionFn sets
    let inclusion ← mkLambdaFVars paramVars inclusionBody
      (binderInfoForMVars := .default)
    let proofBody := mkAppN proofFn (sets ++ hyps)
    let proof ← mkLambdaFVars paramVars proofBody (binderInfoForMVars := .default)
    return ⟨params, #[], fn.outputType, inclusion, proof⟩

structure InclusionM.Context where
  localContext : LocalContext
  localInstances : LocalInstances
  enabledParams : NameSet

structure InclusionM.State where
  ivars : ExprMap IVar := {}
  params : Array InclusionParam := #[]

abbrev InclusionM := ReaderT InclusionM.Context <| StateT InclusionM.State MetaM

instance : MonadBacktrack (Meta.SavedState × InclusionM.State) InclusionM where
  saveState := do return ⟨← Meta.saveState, ← get⟩
  restoreState s := do
    s.1.restore
    set s.2

def InclusionM.run {α : Type} (x : InclusionM α) (enabledParams : NameSet := {}) : MetaM α := do
  let localContext ← getLCtx
  let localInstances ← getLocalInstances
  StateT.run' (ReaderT.run x { localContext, localInstances, enabledParams }) {}

def getParam? (name : Name) : InclusionM (Option Expr) := do
  let registered := (inclusionParamExt.getState (← getEnv)).find? name
  unless registered.isSome do
    throwError "Unknown inclusion parameter '{name}'"
  unless (← read).enabledParams.contains name do return none
  if let some param := (← get).params.find? fun param => param.name == name then
    return some param.exprVar
  let ctx ← read
  let exprVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances (mkConst ``Nat) .syntheticOpaque
  modify fun state => { state with params := state.params.push ⟨name, exprVar⟩ }
  return some exprVar

def mkIVar (e setType toSetInst coverCheck : Expr) : InclusionM IVar := do
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
  let iexpr : IExpr := ⟨⟨eType, setType, toSetInst⟩, e⟩
  let setVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances setType .syntheticOpaque
  let hypType ← iexpr.mkMem setVar
  let hypVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances hypType .syntheticOpaque
  let iVar := { iexpr, setVar, hypVar, coverCheck }
  modify fun state => { state with ivars := state.ivars.insert iVar.expr iVar }
  return iVar

partial def mkCoveredInclusionValueAux (inclusion : Expr) (ivars : Array IVar)
    (i : Nat) (pieces : Array Expr) : MetaM Expr := do
  if h : i < ivars.size then
    let iVar := ivars[i]
    withLocalDeclD `checkedSet iVar.type.setType fun piece => do
      let inner ← mkCoveredInclusionValueAux inclusion ivars (i + 1) (pieces.push piece)
      mkCoverCheck iVar.type iVar.setVar iVar.coverCheck (← mkLambdaFVars #[piece] inner)
  else
    return mkAppN inclusion pieces

partial def mkCoveredInclusionProofAux (target inclusion proof : Expr) (ivars : Array IVar)
    (i : Nat) (pieces pieceHyps : Array Expr) : MetaM Expr := do
  if h : i < ivars.size then
    let iVar := ivars[i]
    withLocalDeclD `checkedSet iVar.type.setType fun piece => do
      let inner ← mkCoveredInclusionValueAux inclusion ivars (i + 1) (pieces.push piece)
      let predicate ← mkLambdaFVars #[piece] inner
      let pieceHypType ← iVar.iexpr.mkMem piece
      withLocalDeclD `checkedSetHyp pieceHypType fun pieceHyp => do
        let next ← mkCoveredInclusionProofAux target inclusion proof ivars (i + 1)
          (pieces.push piece) (pieceHyps.push pieceHyp)
        let pieceProof ← mkLambdaFVars #[piece, pieceHyp] next
        mkAppOptM ``CoverCheck.mem_check
          #[iVar.type.setType, iVar.type.elemType, iVar.type.toSetInst,
            iVar.coverCheck, iVar.setVar, predicate, target, iVar.expr, iVar.hypVar, pieceProof]
  else
    return mkAppN (mkAppN proof pieces) pieceHyps

def mkExprInclusionFunction (e : Expr) (body : ExprInclusionBody) :
    InclusionM ExprInclusionFunction := do
  let state ← get
  let ivars := state.ivars.toArray.map (·.2)
  let paramVars := state.params.map (·.exprVar)
  let setVars := ivars.map (·.setVar)
  let hypVars := ivars.map (·.hypVar)
  let bodyProofType ← inferType body.proofBody
  let some (outputExpr, outputSet, outputToSetInst) := toSetMem? bodyProofType
    | throwError "Inclusion extension returned a proof of {bodyProofType}, expected a containment \
        proof using a `ToSet` instance"
  unless ← isDefEq outputExpr e do
    throwError "Inclusion extension returned a proof for an unexpected expression"
  unless ← isDefEq outputSet body.inclusionBody do
    throwError "Inclusion extension returned a proof for an unexpected inclusion"
  let outputType := ⟨← inferType outputExpr, ← inferType outputSet, outputToSetInst⟩
  let inclusion ← mkLambdaFVars (paramVars ++ setVars) body.inclusionBody
    (binderInfoForMVars := .default)
  let proof ← mkLambdaFVars (paramVars ++ setVars ++ hypVars) body.proofBody
    (binderInfoForMVars := .default)
  return ⟨state.params.map (·.name), ivars.map (·.iexpr), outputType, inclusion, proof⟩

def mkCoveredExprInclusionFunction (e : Expr) (fn : ExprInclusionFunction) :
    InclusionM ExprInclusionFunction := do
  let state ← get
  let ivars := state.ivars.toArray.map (·.2)
  let paramVars := state.params.map (·.exprVar)
  let setVars := ivars.map (·.setVar)
  let hypVars := ivars.map (·.hypVar)
  let inclusion := (mkAppN fn.inclusion paramVars).headBeta
  let inclusionProof := (mkAppN fn.proof paramVars).headBeta
  let inclusionBody ← mkCoveredInclusionValueAux inclusion ivars 0 #[]
  let coveredInclusion ← mkLambdaFVars (paramVars ++ setVars) inclusionBody
    (binderInfoForMVars := .default)
  let proofBody ← mkCoveredInclusionProofAux e inclusion inclusionProof ivars 0 #[] #[]
  let coveredProof ← mkLambdaFVars (paramVars ++ setVars ++ hypVars) proofBody
    (binderInfoForMVars := .default)
  return { fn with inclusion := coveredInclusion, proof := coveredProof }

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

def toExprInclusionFunction (e : Expr) (enabledParams : NameSet := {}) :
    MetaM ExprInclusionFunction :=
  InclusionM.run (enabledParams := enabledParams) do
    let body ← mkExprInclusionBody e
    mkExprInclusionFunction e body

def toCoveredExprInclusionFunction (e : Expr) (enabledParams : NameSet := {}) :
    MetaM ExprInclusionFunction :=
  InclusionM.run (enabledParams := enabledParams) do
    let body ← mkExprInclusionBody e
    mkCoveredExprInclusionFunction e (← mkExprInclusionFunction e body)

end Inclusion
