/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Hypotheses
public meta import Lean.Meta.Native

/-!
# Core implementation of the `inclusion` tactic

**TODO (NOT FOR CODEX)**
-/

@[expose] public meta section

open Lean Meta

namespace Inclusion

structure InclusionConfig where
  /-- Use only the kernel to evaluate the final inclusion check. -/
  kernel : Bool := false
  /-- Use native evaluation and admit its result through an auxiliary axiom. This trusts the Lean
  compiler and any `implemented_by` implementations, and consequently may not be used in mathlib. -/
  native : Bool := false
  /-- Explicit values for inclusion parameters, indexed by their registered names. -/
  paramValues : NameMap Nat := {}
  /-- The enabled inclusion-extension families. -/
  families : Array Name := #[]

-- Explicitly assigning a parameter also enables extensions that request that parameter.
def InclusionConfig.enabledParams (config : InclusionConfig) : NameSet :=
  -- Only the keys matter here; their concrete values are substituted later in `inclusionCore`.
  config.paramValues.foldl (init := {}) fun params name _ => params.insert name

-- A closed inclusion check can be compiled because all of its varying inputs are natural numbers.
abbrev CompiledInclusionCheck := Array Nat → IntervalBool

def compileInclusionCheck (fn : ExprInclusionFunction) : MetaM CompiledInclusionCheck := do
  -- Compilation cannot accept the heterogeneously typed set inputs represented by `iExprs`.
  unless fn.iExprs.isEmpty do
    throwError "Cannot compile an inclusion check before its inclusion hypotheses are supplied"
  -- Construct the expression for the uniform input type `Array Nat`.
  let paramsType ← mkAppM ``Array #[mkConst ``Nat]
  -- Introduce the array that will receive concrete parameter values at compiled runtime.
  withLocalDeclD `params paramsType fun params => do
    -- Replace each named parameter argument by the corresponding array lookup.
    -- `getD` makes each lookup total; callers below always supply the complete array.
    let paramValues ← fn.params.mapIdxM fun i _ =>
      mkAppM ``Array.getD #[params, mkNatLit i, mkNatLit 0]
    -- Apply the closed inclusion function to those runtime parameter expressions.
    let body := mkAppN fn.inclusion paramValues
    -- Package the application as a single function from the parameter array.
    let wrapper ← mkLambdaFVars #[params] body
    -- Give `evalExpr` the explicit type expected of the compiled function.
    let wrapperType ← mkArrow paramsType (mkConst ``IntervalBool)
    -- Compile and evaluate the quoted wrapper into a callable meta-level Lean function.
    unsafe evalExpr CompiledInclusionCheck wrapperType wrapper

def mkCompiledInclusionTrueProof (inclusionExpr : Expr) (compiledCheck : CompiledInclusionCheck)
    (paramValues : Array Nat) : MetaM Expr := do
  -- Run the fast compiled pre-check; only `true` is sufficient for kernel verification.
  match compiledCheck paramValues with
  | .true =>
      -- Return reflexivity at `inclusionExpr`; when this is checked against
      -- `inclusionExpr = true`, the kernel independently reduces `inclusionExpr` to verify that
      -- the compiled result was sound.
      return mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``IntervalBool) inclusionExpr
  | .false =>
      -- A definite negative result cannot prove the requested proposition.
      throwError "The compiled inclusion check returned false"
  | .undetermined =>
      -- An indeterminate result also supplies no certificate of truth.
      throwError "The compiled inclusion check was undetermined"

def diagnoseKernelInclusionFailure (inclusionExpr : Expr) (ex : Exception) : MetaM MessageData := do
  -- Diagnostics are best-effort: failure to reduce here must not hide the original error.
  try
    -- Re-run weak-head reduction to identify the visible final result or blockage.
    let result ← withAtLeastTransparency .default <| whnf inclusionExpr
    -- Give precise messages for the two expected unsuccessful values.
    if result.isConstOf ``IntervalBool.false then
      return "The kernel inclusion check returned false"
    if result.isConstOf ``IntervalBool.undetermined then
      return "The kernel inclusion check was undetermined"
    -- Distinguish an auxiliary-lemma failure from a failure to reduce the check itself.
    if result.isConstOf ``IntervalBool.true then
      return m!"The elaborator reduced the inclusion check to true, but the kernel failed with:\n\
        {indentD ex.toMessageData}"
    -- Display the residual expression when reduction became stuck before reaching a constructor.
    return m!"The kernel could not reduce the inclusion check to true. Reduction became stuck at\
      {indentExpr result}\n\nThe kernel failed with:\n{indentD ex.toMessageData}"
  catch _ =>
    -- Fall back to the original kernel exception if even diagnostic reduction fails.
    return m!"The kernel could not verify the inclusion check:\n{indentD ex.toMessageData}"

def mkKernelInclusionTrueProof (inclusionExpr : Expr) : MetaM Expr := do
  -- This is the equality that the generated auxiliary theorem must prove.
  let expectedType ← mkEq inclusionExpr (mkConst ``IntervalBool.true)
  -- Reflexivity type-checks only if the kernel reduces `inclusionExpr` to true.
  let proof ← mkEqRefl inclusionExpr
  -- Preserve any universe parameters occurring in the generated theorem's type.
  let lemmaLevels := (collectLevelParams {} expectedType).params.toList
  -- Catch kernel-checking failure so it can be replaced by a tactic-specific diagnostic.
  try
    -- Disable asynchronous checking so `mkAuxLemma` reports a kernel failure in this call.
    let lemmaName ← withOptions (Elab.async.set · false) do
      mkAuxLemma lemmaLevels expectedType proof
    -- Return a reference to the now kernel-checked auxiliary theorem.
    return mkConst lemmaName (lemmaLevels.map .param)
  catch ex =>
    -- Delay formatting so the potentially large check is only pretty-printed for the actual error.
    throwError MessageData.ofLazyM (es := #[inclusionExpr]) do
      diagnoseKernelInclusionFailure inclusionExpr ex

def mkNativeInclusionTrueProof (inclusionExpr : Expr) : MetaM Expr := do
  -- Convert the three-valued result into the Boolean proposition expected by `nativeEqTrue`.
  let nativeCheck := mkApp (mkConst ``IntervalBool.isTrue) inclusionExpr
  -- Ask native evaluation for an axiom-backed proof that this Boolean check is true.
  match ← nativeEqTrue `inclusion nativeCheck (axiomDeclRange? := (← getRef)) with
  | .success proof =>
      -- Convert `inclusionExpr.isTrue = true` into the required
      -- `inclusionExpr = IntervalBool.true`.
      mkAppM ``IntervalBool.eq_true_of_isTrue_eq_true #[proof]
  | .notTrue =>
      -- Evaluate the original three-valued result to provide the more informative failure message.
      match ← unsafe evalExpr IntervalBool (mkConst ``IntervalBool) inclusionExpr with
      -- Native evaluation established that neither unsuccessful result proves the goal.
      | .false => throwError "The native inclusion check returned false"
      | .undetermined => throwError "The native inclusion check was undetermined"
      -- This branch would indicate disagreement between the two native evaluations above.
      | .true => throwError "The native inclusion check unexpectedly returned true"

def inclusionCore (goal : Expr) (config : InclusionConfig) : MetaM Expr := do
  if config.kernel && config.native then
    throwError "Cannot simultaneously enable +kernel and +native"
  let goal ← instantiateMVars goal
  unless ← isProp goal do
    throwError "The goal is not a proposition"
  let fn ← toClosedInclusionFunction goal config.enabledParams config.families
  let paramDecls := inclusionParamExt.getState (← getEnv)
  let paramValues ← fn.params.mapM fun name => do
    if let some value := config.paramValues.find? name then
      return value
    let some paramDecl := paramDecls.find? name
      | throwError "Unknown inclusion parameter '{name}'"
    let some value := paramDecl.defaultValue
      | throwError "No value was supplied for inclusion parameter '{name}'"
    return value
  let paramExprs := paramValues.map mkNatLit
  let inclusionExpr := mkAppN fn.inclusion paramExprs
  let inclusionProof ←
    if config.native then
      mkNativeInclusionTrueProof inclusionExpr
    else if config.kernel then
      mkKernelInclusionTrueProof inclusionExpr
    else
      mkCompiledInclusionTrueProof inclusionExpr (← compileInclusionCheck fn) paramValues
  return fn.mkGoalProof goal paramExprs inclusionExpr inclusionProof

end Inclusion
