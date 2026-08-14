module

public meta import Mathlib.Tactic.Inclusion.Experimental.LargeExtensions
public import Mathlib.Tactic.Inclusion.Experimental.Splitting
public meta import Mathlib.Tactic.Inclusion.Experimental.Splitting

set_option linter.style.header false

@[expose] public section

open Lean Meta

namespace Inclusion.Experimental.CheckExpBenchmark

def expInputInterval : Interval Dyadic :=
  ⟨1, 1 + Dyadic.ofIntWithPrec 1 96⟩

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

private meta def timeEvaluation (check : CompiledInclusionFunction) (value : Nat) :
    MetaM (IntervalBool × Nat) := do
  let start ← IO.monoNanosNow
  match check value with
  | .true => return (.true, (← IO.monoNanosNow) - start)
  | .false => return (.false, (← IO.monoNanosNow) - start)
  | .undetermined => return (.undetermined, (← IO.monoNanosNow) - start)

private meta def timeArrayEvaluation (check : CompiledArrayInclusionFunction)
    (paramValues : Array Nat) (paramIdx value : Nat) : MetaM (IntervalBool × Nat) := do
  let start ← IO.monoNanosNow
  match check (paramValues.set! paramIdx value) with
  | .true => return (.true, (← IO.monoNanosNow) - start)
  | .false => return (.false, (← IO.monoNanosNow) - start)
  | .undetermined => return (.undetermined, (← IO.monoNanosNow) - start)

private meta def benchmarkExpSearch : MetaM Unit :=
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let intervalType ← mkAppM ``Interval #[mkConst ``Dyadic]
    let toSetInst ← synthInstance (← mkAppM ``ToSet #[intervalType, mkConst ``Real])
    let hypType ←
      mkToSetMem (mkConst ``Real) intervalType x (mkConst ``expInputInterval) toSetInst
    withLocalDeclD `hx hypType fun _ => do
      let expX ← mkAppM ``Real.exp #[x]
      let difference ← mkAppM ``HSub.hSub #[expX, expX]
      let rhs ← mkAppOptM ``OfScientific.ofScientific
        #[some (mkConst ``Real), none, some (mkNatLit 1), some (mkConst ``true),
          some (mkNatLit 30)]
      let goal ← mkAppM ``LE.le #[difference, rhs]
      let enabledParams := ({} : NameSet).insert `split
      let exprInclusion ← (toExprInclusion goal).run enabledParams #[`core, `real.dyadic]
      let some paramIdx := exprInclusion.params.findIdx? (· == `split)
        | throwError "The split parameter was not used"
      let paramValues ←
        exprInclusion.resolveParamValues (({} : NameMap Nat).insert `split 0)
      let check ← exprInclusion.compile paramValues paramIdx
      let arrayCheck ← compileArray exprInclusion
      -- Force both freshly compiled functions before timing their realistic evaluations.
      match check 0, arrayCheck paramValues with
      | .undetermined, .undetermined => pure ()
      | _, _ => throwError "High-precision exponential warm-up checks returned unexpected results"
      let (arrayResult4, arrayTime4) ← timeArrayEvaluation arrayCheck paramValues paramIdx 4
      let (result4, time4) ← timeEvaluation check 4
      let (arrayResult6, arrayTime6) ← timeArrayEvaluation arrayCheck paramValues paramIdx 6
      let (result6, time6) ← timeEvaluation check 6
      let (arrayResult8, arrayTime8) ← timeArrayEvaluation arrayCheck paramValues paramIdx 8
      let (result8, time8) ← timeEvaluation check 8
      match result4, result6, result8, arrayResult4, arrayResult6, arrayResult8 with
      | .undetermined, .true, .true, .undetermined, .true, .true => pure ()
      | _, _, _, _, _, _ =>
        throwError "High-precision exponential checks returned unexpected results"
      logInfo m!"30-digit exponential unary/array evaluation at `split := 4`: \
        {time4 / 1000}μs / {arrayTime4 / 1000}μs"
      logInfo m!"30-digit exponential unary/array evaluation at `split := 6`: \
        {time6 / 1000}μs / {arrayTime6 / 1000}μs"
      logInfo m!"30-digit exponential unary/array evaluation at `split := 8`: \
        {time8 / 1000}μs / {arrayTime8 / 1000}μs"
      let config : InclusionConfig := { families := #[`core, `real.dyadic] }
      let start ← IO.monoMsNow
      let result ← inclusionCheckCore goal config (some { name := `split, max := 100 })
      let finish ← IO.monoMsNow
      unless result == some (`split, 6) do
        throwError "High-precision exponential search returned {result}, expected `split := 6`"
      logInfo m!"30-digit exponential search through `split := search[100]`: \
        {finish - start}ms"

set_option inclusion.large.precision 120 in
run_meta benchmarkExpSearch

end Inclusion.Experimental.CheckExpBenchmark
