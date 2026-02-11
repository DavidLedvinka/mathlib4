import Mathlib.Tactic.Linarith
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Rify

public meta section

namespace Mathlib.Tactic.Linarith

/-! ### Preprocessing -/

open Lean Std TreeSet
open Elab Tactic Meta
open Rify NNReal

/--
`isNNRealProp tp` is true iff `tp` is an inequality or equality between nonnegative real numbers
or the negation thereof.
-/
partial def isNNRealProp (e : Expr) : MetaM Bool := succeeds do
  let (_, _, .const ``NNReal [], _, _) ← e.ineqOrNotIneq? | failure

/-- If `e` is of the form `((n : ℝ≥0) : C)`, `NNReal.toReal e` returns `⟨n, C⟩`. -/
def isNNRealtoReal (e : Expr) : Option Expr :=
  match e with
  | .app (.const ``NNReal.toReal _) n => some n
  | _ => none

/--
`getNatComparisons e` returns a list of all subexpressions of `e` of the form `((t : ℝ≥0) : C)`.
-/
partial def getNNRealComparisons (e : Expr) : List Expr :=
  match isNNRealtoReal e with
  | some x => [x]
  | none => match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => getNNRealComparisons a ++ getNNRealComparisons b
    | (``HMul.hMul, #[_, _, _, _, a, b]) => getNNRealComparisons a ++ getNNRealComparisons b
    | (``HSub.hSub, #[_, _, _, _, a, b]) => getNNRealComparisons a ++ getNNRealComparisons b
    | (``Neg.neg, #[_, _, a]) => getNNRealComparisons a
    | _ => []

/-- If `e : ℝ≥0`, returns a proof of `0 ≤ (e : C)`. -/
def mk_toReal_nonneg_prf (e : Expr) : MetaM (Option Expr) :=
  try commitIfNoEx (mkAppM ``NNReal.coe_nonneg #[e])
  catch e => do
    trace[linarith] "Got exception when using `coe_nonneg` {e.toMessageData}"
    return none

initialize nnRealToRealTransform.set fun g l => do
    let l ← l.mapM fun h => do
      let t ← whnfR (← instantiateMVars (← inferType h))
      if ← isNNRealProp t then
        let (some (h', t'), _) ← Term.TermElabM.run' (run_for g (rifyProof none h t))
          | throwError "rifyProof failed on {h}"
        if ← succeeds t'.ineqOrNotIneq? then
          pure h'
        else
          pure h
      else
        pure h
    withNewMCtxDepth <| AtomM.run .reducible do
    let nonnegs ← l.foldlM (init := ∅) fun (es : TreeSet ℕ) h => do
      try
        let (_, _, a, b) ← (← inferType h).ineq?
        let getIndex (e : Expr) : AtomM ℕ := return (← AtomM.addAtom e).1
        let indices_a ← (getNNRealComparisons a).mapM getIndex
        let indices_b ← (getNNRealComparisons b).mapM getIndex
        pure <| (es.insertMany indices_a).insertMany indices_b
      catch _ => pure es
    let atoms : Array Expr := (← get).atoms
    let nonneg_pfs : List Expr ← nonnegs.toList.filterMapM fun n => do
      mk_toReal_nonneg_prf atoms[n]!
    pure [(g, nonneg_pfs ++ l)]

end  Mathlib.Tactic.Linarith
