module

public meta import Mathlib.Tactic.Inclusion.Core.Inclusion

set_option linter.style.header false

@[expose] public meta section

open Lean Meta Elab Term

namespace Inclusion

/-- A bound for one of the inclusion variables requested by the target computation. -/
structure InclusionHypResult where
  expr : Expr
  bound : ExprInclusionFunction

structure InclusionHypM.Context where
  requested : ExprMap IExpr
  requestedArray : Array IExpr
  enabledParams : NameSet

structure InclusionHypM.State where
  bounds : ExprMap (Array ExprInclusionFunction) := {}
  cache : ExprMap ExprInclusionFunction := {}

abbrev InclusionHypM := ReaderT InclusionHypM.Context <| StateT InclusionHypM.State MetaM

instance : MonadBacktrack (Meta.SavedState × InclusionHypM.State) InclusionHypM where
  saveState := do return ⟨← Meta.saveState, ← get⟩
  restoreState s := do
    s.1.restore
    set s.2

def InclusionHypM.run {α : Type} (x : InclusionHypM α)
    (requested : Array IExpr) (enabledParams : NameSet) : MetaM α := do
  let requestedMap := requested.foldl
    (fun result iexpr => result.insert iexpr.expr iexpr) ({} : ExprMap IExpr)
  StateT.run' (ReaderT.run x ⟨requestedMap, requested, enabledParams⟩) {}

def isDefEqWithoutAssignment (a b : Expr) : MetaM Bool := do
  let saved ← Meta.saveState
  try
    let result ← withNewMCtxDepth <| isDefEq a b
    saved.restore
    return result
  catch err =>
    saved.restore
    throw err

/-- Find the canonical target inclusion variable definitionally equal to `e`. Exact expression
matching is attempted first and does not invoke the elaborator. -/
def requestedIVar? (e : Expr) : InclusionHypM (Option IExpr) := do
  let ctx ← read
  if let some iexpr := ctx.requested[e]? then
    return some iexpr
  for requested in ctx.requestedArray do
    if ← isDefEqWithoutAssignment e requested.expr then
      return some requested
  return none

def ensureOutputType (actual expected : IType) : MetaM Unit := do
  unless ← isDefEqWithoutAssignment actual.elemType expected.elemType do
    throwError "Hypothesis bound has expression type {actual.elemType}, expected \
      {expected.elemType}"
  unless ← isDefEqWithoutAssignment actual.setType expected.setType do
    throwError "Hypothesis bound has set type {actual.setType}, expected {expected.setType}"
  unless ← isDefEqWithoutAssignment actual.toSetInst expected.toSetInst do
    throwError "Hypothesis bound uses an unexpected `ToSet` instance"

/-- Construct and cache a reusable inclusion function for a hypothesis endpoint. Such an endpoint
must be closed with respect to inclusion variables; otherwise using it would merely replace one
unknown bound by another. -/
def mkHypInclusionFunction (e : Expr)
    (expected : IType) : InclusionHypM ExprInclusionFunction := do
  let fn ← if let some fn := (← get).cache[e]? then
    pure fn
  else
    let fn ← toExprInclusionFunction e (← read).enabledParams
    modify fun state => { state with cache := state.cache.insert e fn }
    pure fn
  unless fn.iexprs.isEmpty do
    throwError "The prospective hypothesis bound {e} depends on unbounded expressions"
  if fn.inclusion.hasFVar then
    throwError "The computational part of the prospective hypothesis bound {e} contains a free \
      variable"
  if fn.inclusion.hasMVar then
    throwError "The computational part of the prospective hypothesis bound {e} contains a \
      metavariable"
  ensureOutputType fn.outputType expected
  return fn

def addInclusionHypResult (result : InclusionHypResult) : InclusionHypM Unit := do
  let some iexpr ← requestedIVar? result.expr | return
  ensureOutputType result.bound.outputType iexpr.iVarType
  modify fun state => { state with bounds := state.bounds.alter iexpr.expr fun
    | some bounds => bounds.push result.bound
    | none => #[result.bound] }

structure InclusionHypRule where
  name : Name := by exact decl_name%
  derive (h : Expr) : InclusionHypM (Array InclusionHypResult)
  priority : Nat := eval_prio default

def mkInclusionHypRule (n : Name) : ImportM InclusionHypRule := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck InclusionHypRule opts ``InclusionHypRule n

abbrev InclusionHypRuleEntry := Array (Array DiscrTree.Key) × Name

structure InclusionHypRules where
  tree : DiscrTree InclusionHypRule := {}
  erased : PHashSet Name := {}
  deriving Inhabited

def InclusionHypRules.eraseCore (rules : InclusionHypRules) (declName : Name) : InclusionHypRules :=
  { rules with erased := rules.erased.insert declName }

def InclusionHypRules.erase {m : Type → Type} [Monad m] [MonadError m]
    (rules : InclusionHypRules) (declName : Name) : m InclusionHypRules := do
  unless rules.tree.values.any (·.name == declName) && !rules.erased.contains declName do
    throwError "'{declName}' does not have [inclusionHypRule] attribute"
  return rules.eraseCore declName

initialize inclusionHypRule :
    ScopedEnvExtension InclusionHypRuleEntry (InclusionHypRuleEntry × InclusionHypRule)
      InclusionHypRules ←
  have : BEq InclusionHypRule := ⟨fun _ _ ↦ false⟩
  let insert kss v dt := kss.foldl (fun dt ks ↦ dt.insertKeyValue ks v) dt
  registerScopedEnvExtension {
    mkInitial := pure {}
    ofOLeanEntry := fun _ e@(_, n) ↦ return (e, ← mkInclusionHypRule n)
    toOLeanEntry := (·.1)
    addEntry := fun { tree, erased } ((kss, n), rule) ↦
      { tree := insert kss rule tree, erased := erased.erase n }
  }

syntax (name := inclusionHypRuleAttr) "inclusionHypRule" term,+ : attr

/-- The `inclusionHypRule` attribute registers a backward hypothesis rule. -/
initialize registerBuiltinAttribute {
  name := `inclusionHypRuleAttr
  descr := "adds a backward rule for deriving inclusion-variable bounds from hypotheses"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| inclusionHypRule $es,*) => do
      let env ← getEnv
      ensureAttrDeclIsMeta `inclusionHypRule declName kind
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute `inclusionHypRule`, declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return
      let rule ← mkInclusionHypRule declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx ↦ do
        let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
      inclusionHypRule.add ((keys, declName), rule) kind
    | _ => throwUnsupportedSyntax
  erase := fun declName => do
    let rules := inclusionHypRule.getState (← getEnv)
    let rules ← rules.erase declName
    modifyEnv fun env => inclusionHypRule.modifyState env fun _ => rules
}

def directInclusionHyp? (h type : Expr) : InclusionHypM (Option InclusionHypResult) := do
  let some (expr, set, toSetInst) := toSetMem? type | return none
  let some iexpr ← requestedIVar? expr | return none
  let iVarType := iexpr.iVarType
  unless ← isDefEqWithoutAssignment (← inferType set) iVarType.setType do return none
  unless ← isDefEqWithoutAssignment toSetInst iVarType.toSetInst do return none
  if set.hasFVar || set.hasMVar then
    trace[Tactic.inclusion] "Ignoring non-closed direct bound {type}"
    return none
  return some ⟨iexpr.expr, ⟨#[], #[], iVarType, set, h⟩⟩

def runInclusionHypRules (h type : Expr) : InclusionHypM Unit := do
  let rules := inclusionHypRule.getState (← getEnv)
  let matchedRules ← rules.tree.getMatch type
  let matchedRules := matchedRules.qsort (fun rule₁ rule₂ ↦ rule₁.priority < rule₂.priority)
  for rule in matchedRules do
    if !rules.erased.contains rule.name then
      let saved ← saveState
      try
        for result in ← rule.derive h do
          addInclusionHypResult result
        recordExtraModUseFromDecl (isMeta := true) rule.name
        trace[Tactic.inclusion] "{rule.name} processed {type}"
      catch err =>
        trace[Tactic.inclusion] "Failed to apply {rule.name} to {type} : {err.toMessageData}"
        restoreState saved

def mkUniversalInclusionBound (expr : Expr)
    (iVarType : IType) : MetaM ExprInclusionFunction := do
  let universeType ← mkAppOptM ``Univ
    #[iVarType.setType, iVarType.elemType, iVarType.toSetInst]
  let universeInst ← try synthInstance universeType catch _ =>
    throwError "No hypothesis bounds were found for {expr}, and no `Univ` instance is \
      registered for {iVarType.setType}"
  let set ← mkAppOptM ``Univ.univ
    #[iVarType.setType, iVarType.elemType, iVarType.toSetInst, universeInst]
  let proof ← mkAppOptM ``Univ.mem_univ
    #[iVarType.setType, iVarType.elemType, iVarType.toSetInst, universeInst, expr]
  return ⟨#[], #[], iVarType, set, proof⟩

def combineInclusionBounds (expr : Expr) (iVarType : IType)
    (bounds : Array ExprInclusionFunction) : MetaM ExprInclusionFunction := do
  if bounds.isEmpty then
    return ← mkUniversalInclusionBound expr iVarType
  let mut params := #[]
  for bound in bounds do
    unless bound.iexprs.isEmpty do
      throwError "A hypothesis bound for {expr} contains inclusion variables"
    ensureOutputType bound.outputType iVarType
    params := mergeInclusionParams params bound.params
  withInclusionParams params fun paramVars => do
    let mut sets := Array.mkEmpty bounds.size
    let mut hyps := Array.mkEmpty bounds.size
    for bound in bounds do
      let args ← inclusionParamArgs params paramVars bound.params
      sets := sets.push ((mkAppN bound.inclusion args).headBeta)
      hyps := hyps.push ((mkAppN bound.proof args).headBeta)
    let mut set := sets[0]!
    let mut hyp := hyps[0]!
    if bounds.size > 1 then
      let refinerType ← mkAppOptM ``Refine
        #[iVarType.setType, iVarType.elemType, iVarType.toSetInst]
      let refiner ← try synthInstance refinerType catch _ =>
        throwError "Multiple hypothesis bounds were found for {expr}, but no `Refine` instance \
          is registered for {iVarType.setType}"
      for _h : i in [1:bounds.size] do
        let nextSet := sets[i]!
        let nextHyp := hyps[i]!
        set ← mkAppOptM ``Refine.refine
          #[iVarType.setType, iVarType.elemType, iVarType.toSetInst, refiner, set, nextSet]
        hyp ← mkAppM ``Refine.mem_refine #[hyp, nextHyp]
    let inclusion ← mkLambdaFVars paramVars set (binderInfoForMVars := .default)
    let proof ← mkLambdaFVars paramVars hyp (binderInfoForMVars := .default)
    return ⟨params, #[], iVarType, inclusion, proof⟩

/-- Derive and combine one closed bound for every inclusion variable requested by `fn`. -/
def mkInclusionHypBounds (fn : ExprInclusionFunction)
    (enabledParams : NameSet) : MetaM (Array ExprInclusionFunction) := do
  if fn.iexprs.isEmpty then
    return #[]
  InclusionHypM.run (requested := fn.iexprs) (enabledParams := enabledParams) do
    for ldecl in ← getLCtx do
      unless ldecl.isImplementationDetail do
        let h := ldecl.toExpr
        let type ← instantiateMVars ldecl.type
        if let some result ← directInclusionHyp? h type then
          addInclusionHypResult result
        runInclusionHypRules h type
    let state ← get
    fn.iexprs.mapM fun iexpr =>
      combineInclusionBounds iexpr.expr iexpr.iVarType (state.bounds[iexpr.expr]?.getD #[])

end Inclusion
