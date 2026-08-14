module

public import Mathlib.Tactic.Inclusion.Experimental.Splitting
public meta import Mathlib.Tactic.Inclusion.Experimental.Splitting

set_option linter.style.header false

@[expose] public section

open Lean Meta

namespace Inclusion.Experimental.CheckCompilationBenchmark

def unitInterval : Interval Dyadic := ⟨1, 2⟩

private abbrev CompiledArrayInclusionFunction := Array Nat → IntervalBool

private meta def compileArray (exprInclusion : ExprInclusion) :
    MetaM CompiledArrayInclusionFunction := do
  let paramsType ← mkAppM ``Array #[mkConst ``Nat]
  withLocalDeclD `params paramsType fun params => do
    let paramExprs ← exprInclusion.params.mapIdxM fun i _ =>
      mkAppM ``getElem! #[params, mkNatLit i]
    let inclusion ← mkLambdaFVars #[params] (mkAppN exprInclusion.inclusion paramExprs)
    let inclusionType ← mkArrow paramsType (mkConst ``IntervalBool)
    unsafe evalExpr CompiledArrayInclusionFunction inclusionType inclusion

private meta def sameResult : IntervalBool → IntervalBool → Bool
  | .true, .true | .false, .false | .undetermined, .undetermined => true
  | _, _ => false

private meta def benchmarkPackedCompilation : MetaM Unit :=
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let intervalType ← mkAppM ``Interval #[mkConst ``Dyadic]
    let toSetInst ← synthInstance (← mkAppM ``ToSet #[intervalType, mkConst ``Real])
    let hypType ← mkToSetMem (mkConst ``Real) intervalType x (mkConst ``unitInterval) toSetInst
    withLocalDeclD `hx hypType fun _ => do
      let difference ← mkAppM ``HSub.hSub #[x, x]
      let one ← mkNumeral (mkConst ``Real) 1
      let denominator ← mkNumeral (mkConst ``Real) 64
      let rhs ← mkAppM ``HDiv.hDiv #[one, denominator]
      let goal ← mkAppM ``LE.le #[difference, rhs]
      let enabledParams := ({} : NameSet).insert `split
      let exprInclusion ← (toExprInclusion goal).run enabledParams #[`core, `real.dyadic]
      let some paramIdx := exprInclusion.params.findIdx? (· == `split)
        | throwError "The split parameter was not used"
      let paramValues ←
        exprInclusion.resolveParamValues (({} : NameMap Nat).insert `split 0)
      -- These are the candidates visited by the search for this goal, in evaluation order.
      let candidates := #[0, 1, 2, 4, 8, 6, 5]

      let parameterizedStart ← IO.monoMsNow
      let check ← exprInclusion.compile paramValues paramIdx
      let mut parameterizedResults := Array.emptyWithCapacity candidates.size
      for value in candidates do
        match check value with
        | .true => parameterizedResults := parameterizedResults.push .true
        | .false => parameterizedResults := parameterizedResults.push .false
        | .undetermined => parameterizedResults := parameterizedResults.push .undetermined
      let parameterizedTime ← IO.monoMsNow

      let arrayStart := parameterizedTime
      let arrayCheck ← compileArray exprInclusion
      let mut arrayResults := Array.emptyWithCapacity candidates.size
      for value in candidates do
        match arrayCheck (paramValues.set! paramIdx value) with
        | .true => arrayResults := arrayResults.push .true
        | .false => arrayResults := arrayResults.push .false
        | .undetermined => arrayResults := arrayResults.push .undetermined
      let arrayTime ← IO.monoMsNow

      let exactStart := arrayTime
      let mut exactResults := Array.emptyWithCapacity candidates.size
      for value in candidates do
        let values := paramValues.set! paramIdx value
        let inclusionExpr := mkAppN exprInclusion.inclusion (values.map mkNatLit)
        match ← compileInclusionCheck inclusionExpr with
        | .true => exactResults := exactResults.push .true
        | .false => exactResults := exactResults.push .false
        | .undetermined => exactResults := exactResults.push .undetermined
      let exactTime ← IO.monoMsNow

      for i in [:candidates.size] do
        match parameterizedResults[i]?, arrayResults[i]?, exactResults[i]? with
        | some parameterized, some array, some exact =>
          unless sameResult parameterized exact do
            throwError "Parameterized and separately compiled checks returned different results"
          unless sameResult array exact do
            throwError "Array-packed and separately compiled checks returned different results"
        | _, _, _ => throwError "A benchmark result array had an unexpected size"
      logInfo m!"one unary compilation plus {candidates.size} evaluations: \
        {parameterizedTime - parameterizedStart}ms"
      logInfo m!"one array-packed compilation plus {candidates.size} evaluations: \
        {arrayTime - arrayStart}ms"
      logInfo m!"{candidates.size} separately compiled exact checks: {exactTime - exactStart}ms"

run_meta benchmarkPackedCompilation

end Inclusion.Experimental.CheckCompilationBenchmark
