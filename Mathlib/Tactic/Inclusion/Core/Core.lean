module

public meta import Mathlib.Tactic.Inclusion.Core.Hypotheses

set_option linter.style.header false

@[expose] public meta section

open Lean Meta Elab Tactic

namespace Inclusion

structure InclusionConfig where
  enabledParams : NameSet := {}
  values : NameMap Nat := {}

def mkGoalInclusionFunction (target : Expr) (config : InclusionConfig) :
    MetaM ExprInclusionFunction := do
  unless ← isProp target do
    throwError "The target is not a proposition"
  let fn ← toCoveredExprInclusionFunction target config.enabledParams
  if fn.iexprs.isEmpty then
    return fn
  fn.closeWithBounds (← mkInclusionHypBounds fn config.enabledParams)

abbrev CompiledInclusionCheck := Array Nat → IntervalBool

def compileInclusionCheck (fn : ExprInclusionFunction) : MetaM CompiledInclusionCheck := do
  unless fn.iexprs.isEmpty do
    throwError "Cannot compile an inclusion check before its inclusion variables are bounded"
  let paramsType ← mkAppM ``Array #[mkConst ``Nat]
  withLocalDeclD `params paramsType fun params => do
    let paramValues ← fn.params.mapIdxM fun i _ =>
      mkAppM ``Array.getD #[params, mkNatLit i, mkNatLit 0]
    let body := mkAppN fn.inclusion paramValues
    let wrapper ← mkLambdaFVars #[params] body
    let wrapperType ← mkArrow paramsType (mkConst ``IntervalBool)
    unsafe evalExpr CompiledInclusionCheck wrapperType wrapper

def mkInclusionTrueProof (checkValue : Expr) (compiledCheck : CompiledInclusionCheck)
    (paramValues : Array Nat) : MetaM Expr := do
  let inclusionResult := compiledCheck paramValues
  match inclusionResult with
  | IntervalBool.true =>
      return mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``IntervalBool) checkValue
  | IntervalBool.false =>
      throwError "The compiled inclusion check returned false"
  | IntervalBool.undetermined =>
      throwError "The compiled inclusion check was undetermined"

def inclusionCore (g : MVarId) (config : InclusionConfig) : MetaM Expr := do
  let target ← instantiateMVars (← g.getType)
  let fn ← mkGoalInclusionFunction target config
  let paramValues ← fn.params.mapM fun name => match config.values.find? name with
    | some value => pure value
    | none => throwError "No value was supplied for enabled inclusion parameter '{name}'"
  let paramExprs := paramValues.map mkNatLit
  let checkValue := mkAppN fn.inclusion paramExprs
  let checkTrue ← mkInclusionTrueProof checkValue (← compileInclusionCheck fn) paramValues
  let memProof := mkAppN fn.proof paramExprs
  return mkAppN (mkConst ``true_of_mem_intervalBool_eq_true)
    #[target, checkValue, memProof, checkTrue]

def defaultInclusionConfig : CoreM InclusionConfig := do
  let mut config : InclusionConfig := {}
  for param in (inclusionParamExt.getState (← getEnv)).decls do
    if param.enabledByDefault then
      config := {
        enabledParams := config.enabledParams.insert param.name
        values := config.values.insert param.name param.defaultValue
      }
  return config

declare_syntax_cat inclusionSetting
syntax ident " := " num : inclusionSetting

def parseInclusionConfig (settings : Array Syntax) : TacticM InclusionConfig := do
  let mut config ← defaultInclusionConfig
  let mut specified : NameSet := {}
  let params := inclusionParamExt.getState (← getEnv)
  for setting in settings do
    let `(inclusionSetting| $name:ident := $value:num) := setting
      | throwUnsupportedSyntax
    let name := name.getId
    unless (params.find? name).isSome do
      throwError "Unknown inclusion parameter '{name}'"
    if specified.contains name then
      throwError "Inclusion parameter '{name}' was specified more than once"
    specified := specified.insert name
    config := {
      enabledParams := config.enabledParams.insert name
      values := config.values.insert name value.getNat
    }
  return config

def inclusionTactic (config : InclusionConfig) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  g.assign (← inclusionCore g config)
  replaceMainGoal []

elab "inclusion" : tactic => do
  inclusionTactic (← defaultInclusionConfig)

elab "inclusion" "[" settings:inclusionSetting,* "]" : tactic => do
  inclusionTactic (← parseInclusionConfig settings.getElems)

end Inclusion
