/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Hypotheses
meta import Lean.Elab.ConfigEval
public meta import Lean.Meta.Native
meta import Lean.Meta.Tactic.AuxLemma

/-!
# Core implementation of the `inclusion` tactic

**TODO (NOT FOR CODEX)**
-/

@[expose] public meta section

open Lean Meta Elab Tactic
open Lean.Elab.ConfigEval
open Lean.Parser.Tactic

namespace Inclusion

/-- Test whether `a` and `b` are definitionally equal without retaining any metavariable
assignments made by the test. -/
def isDefEqWithoutAssignment (a b : Expr) : MetaM Bool :=
  withoutModifyingState <| withNewMCtxDepth <| isDefEq a b

/-- Check that two inclusion types are definitionally equal, including their chosen `ToSet`
instances. -/
def ensureOutputType (actual expected : IType) : MetaM Unit := do
  unless ← isDefEqWithoutAssignment actual.elemType expected.elemType do
    throwError "Inclusion function has expression type {actual.elemType}, expected \
      {expected.elemType}"
  unless ← isDefEqWithoutAssignment actual.setType expected.setType do
    throwError "Inclusion function has set type {actual.setType}, expected {expected.setType}"
  unless ← isDefEqWithoutAssignment actual.toSetInst expected.toSetInst do
    throwError "Inclusion function uses an unexpected `ToSet` instance"

/-- Close an inclusion function by substituting a closed inclusion function for every inclusion
variable, with the entries of `hyps` corresponding in order to `fn.iExprs`. Parameter names are
merged, so all computations remain reusable while their concrete natural-number values are chosen
later. -/
def ExprInclusionFunction.closeWithHyps (fn : ExprInclusionFunction)
    (hyps : Array ExprInclusionFunction) : MetaM ExprInclusionFunction := do
  unless fn.iExprs.size = hyps.size do
    throwError "Internal error: the inclusion function and its hypotheses have different lengths"
  if fn.iExprs.isEmpty then
    return fn
  let (params, argIndices) :=
    mergeInclusionParams (#[fn.params] ++ hyps.map (·.params))
  withInclusionParams params fun paramVars => do
    let fnParamArgs := argIndices[0]!.map fun i => paramVars[i]!
    let inclusionFn := (mkAppN fn.inclusion fnParamArgs).headBeta
    let proofFn := (mkAppN fn.proof fnParamArgs).headBeta
    let mut sets := Array.emptyWithCapacity hyps.size
    let mut proofs := Array.emptyWithCapacity hyps.size
    for _h : i in [:hyps.size] do
      let hyp := hyps[i]
      let expected := fn.iExprs[i]!
      ensureOutputType hyp.outputType expected.iType
      let hypParamArgs := argIndices[i + 1]!.map fun j => paramVars[j]!
      sets := sets.push ((mkAppN hyp.inclusion hypParamArgs).headBeta)
      proofs := proofs.push ((mkAppN hyp.proof hypParamArgs).headBeta)
    let inclusionBody := mkAppN inclusionFn sets
    let inclusion ← mkLambdaFVars paramVars inclusionBody
    let proofBody := mkAppN proofFn (sets ++ proofs)
    let proof ← mkLambdaFVars paramVars proofBody
    return ⟨params, #[], fn.outputType, inclusion, proof⟩

structure InclusionConfig where
  /-- Use only the kernel to evaluate the final inclusion check. -/
  kernel : Bool := false
  /-- Use native evaluation and admit its result through an auxiliary axiom. This trusts the Lean
  compiler and any `implemented_by` implementations, and consequently may not be used in mathlib. -/
  native : Bool := false
  /-- Explicit values for inclusion parameters, indexed by their registered names. -/
  paramValues : NameMap Nat := {}
  /-- The enabled inclusion-extension families. -/
  families : NameSet := {}

def InclusionConfig.enabledParams (config : InclusionConfig) : NameSet :=
  config.paramValues.foldl (init := {}) fun params name _ => params.insert name

def mkGoalInclusionFunction (target : Expr) (config : InclusionConfig) :
    MetaM ExprInclusionFunction := do
  unless ← isProp target do
    throwError "The target is not a proposition"
  let enabledParams := config.enabledParams
  let fn ← toExprInclusionFunction target (enabledParams := enabledParams)
    (enabledFamilies := config.families)
  if fn.iExprs.isEmpty then
    return fn
  fn.closeWithHyps (← mkHyps fn enabledParams (enabledFamilies := config.families))

abbrev CompiledInclusionCheck := Array Nat → IntervalBool

def compileInclusionCheck (fn : ExprInclusionFunction) : MetaM CompiledInclusionCheck := do
  unless fn.iExprs.isEmpty do
    throwError "Cannot compile an inclusion check before its inclusion hypotheses are supplied"
  let paramsType ← mkAppM ``Array #[mkConst ``Nat]
  withLocalDeclD `params paramsType fun params => do
    let paramValues ← fn.params.mapIdxM fun i _ =>
      mkAppM ``Array.getD #[params, mkNatLit i, mkNatLit 0]
    let body := mkAppN fn.inclusion paramValues
    let wrapper ← mkLambdaFVars #[params] body
    let wrapperType ← mkArrow paramsType (mkConst ``IntervalBool)
    unsafe evalExpr CompiledInclusionCheck wrapperType wrapper

def mkCompiledInclusionTrueProof (checkValue : Expr) (compiledCheck : CompiledInclusionCheck)
    (paramValues : Array Nat) : MetaM Expr := do
  let inclusionResult := compiledCheck paramValues
  match inclusionResult with
  | IntervalBool.true =>
      return mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``IntervalBool) checkValue
  | IntervalBool.false =>
      throwError "The compiled inclusion check returned false"
  | IntervalBool.undetermined =>
      throwError "The compiled inclusion check was undetermined"

def diagnoseKernelInclusionFailure (checkValue : Expr) (ex : Exception) : MetaM MessageData := do
  try
    let result ← withAtLeastTransparency .default <| whnf checkValue
    if result.isConstOf ``IntervalBool.false then
      return "The kernel inclusion check returned false"
    if result.isConstOf ``IntervalBool.undetermined then
      return "The kernel inclusion check was undetermined"
    if result.isConstOf ``IntervalBool.true then
      return m!"The elaborator reduced the inclusion check to true, but the kernel failed with:\n\
        {indentD ex.toMessageData}"
    return m!"The kernel could not reduce the inclusion check to true. Reduction became stuck at\
      {indentExpr result}\n\nThe kernel failed with:\n{indentD ex.toMessageData}"
  catch _ =>
    return m!"The kernel could not verify the inclusion check:\n{indentD ex.toMessageData}"

def mkKernelInclusionTrueProof (checkValue : Expr) : MetaM Expr := do
  let expectedType ← mkEq checkValue (mkConst ``IntervalBool.true)
  let proof ← mkEqRefl checkValue
  let lemmaLevels := (collectLevelParams {} expectedType).params.toList
  try
    let lemmaName ← withOptions (Elab.async.set · false) do
      mkAuxLemma lemmaLevels expectedType proof
    return mkConst lemmaName (lemmaLevels.map .param)
  catch ex =>
    throwError MessageData.ofLazyM (es := #[checkValue]) do
      diagnoseKernelInclusionFailure checkValue ex

def mkNativeInclusionTrueProof (checkValue : Expr)
    (axiomDeclRange? : Option Syntax := none) : MetaM Expr := do
  let nativeCheck := mkApp (mkConst ``IntervalBool.isTrue) checkValue
  match ← nativeEqTrue `inclusion nativeCheck (axiomDeclRange? := axiomDeclRange?) with
  | .success proof =>
      mkAppM ``IntervalBool.eq_true_of_isTrue_eq_true #[proof]
  | .notTrue =>
      let result ← unsafe evalExpr IntervalBool (mkConst ``IntervalBool) checkValue
      match result with
      | .false => throwError "The native inclusion check returned false"
      | .undetermined => throwError "The native inclusion check was undetermined"
      | .true => throwError "The native inclusion check unexpectedly returned true"

def inclusionCore (g : MVarId) (config : InclusionConfig)
    (axiomDeclRange? : Option Syntax := none) : MetaM Expr := do
  if config.kernel && config.native then
    throwError "Cannot simultaneously set both `+kernel` and `+native`"
  let target ← instantiateMVars (← g.getType)
  let fn ← mkGoalInclusionFunction target config
  let registeredParams := inclusionParamExt.getState (← getEnv)
  let paramValues ← fn.params.mapM fun name => match config.paramValues.find? name with
    | some value => pure value
    | none => match registeredParams.find? name with
      | some param => do
        unless param.enabledByDefault do
          throwError "No value was supplied for inclusion parameter '{name}'"
        pure param.defaultValue
      | none => throwError "Unknown inclusion parameter '{name}'"
  let paramExprs := paramValues.map mkNatLit
  let checkValue := mkAppN fn.inclusion paramExprs
  let checkTrue ←
    if config.native then
      mkNativeInclusionTrueProof checkValue axiomDeclRange?
    else if config.kernel then
      mkKernelInclusionTrueProof checkValue
    else
      mkCompiledInclusionTrueProof checkValue (← compileInclusionCheck fn) paramValues
  let memProof := mkAppN fn.proof paramExprs
  return mkAppN (mkConst ``true_of_mem_intervalBool_eq_true)
    #[target, checkValue, memProof, checkTrue]

declare_syntax_cat inclusionSetting
syntax ident " := " num : inclusionSetting
syntax "+" ident : inclusionSetting

def parseInclusionConfig (config : InclusionConfig)
    (settings : Array Syntax) : TacticM InclusionConfig := do
  let mut config := config
  let params := inclusionParamExt.getState (← getEnv)
  for setting in settings do
    match setting with
    | `(inclusionSetting| $name:ident := $value:num) =>
      let name := name.getId
      unless (params.find? name).isSome do
        throwError "Unknown inclusion parameter '{name}'"
      if config.paramValues.contains name then
        throwError "Inclusion parameter '{name}' was specified more than once"
      config := { config with paramValues := config.paramValues.insert name value.getNat }
    | `(inclusionSetting| +$family:ident) =>
      let family := family.getId
      let env ← getEnv
      let inclusionFamilies := (inclusionExt.getState env).tree
      let hypothesisFamilies := (hypothesisExt.getState env).tree
      unless inclusionFamilies.contains family || hypothesisFamilies.contains family do
        throwError "Unknown inclusion family '{family}'"
      if config.families.contains family then
        throwError "Inclusion family '{family}' was enabled more than once"
      config := { config with families := config.families.insert family }
    | _ => throwUnsupportedSyntax
  return config

def inclusionTactic (config : InclusionConfig) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  g.assign (← inclusionCore g config (some (← getRef)))
  replaceMainGoal []

syntax (name := inclusion) "inclusion" optConfig (" [" inclusionSetting,* "]")? : tactic

def parseInclusionOptions (config : InclusionConfig) (cfg : Syntax) : TacticM InclusionConfig :=
  foldConfigM config cfg
    (onErr := fun _ stx => throwErrorAt stx "Invalid inclusion configuration") fun config item => do
      let value ← match item.bool? with
        | some value => pure value
        | none => evalTermOrExprWithElab ⟨item.value⟩
      match item.getCurrOptionName with
      | `kernel => return { config with kernel := value }
      | `native => return { config with native := value }
      | _ => item.throwInvalidOption (some ``InclusionConfig)

elab_rules : tactic
  | `(tactic| inclusion $cfg:optConfig $[[$settings,*]]?) => do
      let families : NameSet := .ofList [`core, `real.dyadic]
      let config ← parseInclusionOptions { families } cfg
      let settings := (settings.map (·.getElems)).getD #[]
      inclusionTactic (← parseInclusionConfig config settings)

end Inclusion
