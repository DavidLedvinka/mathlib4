/-
Copyright (c) 2018 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Linarith
public meta import Mathlib.Tactic.Rify
public import Mathlib.Data.NNReal.Basic

/-!
# TODO Docstring
-/

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

/-- If `e` is of the form `((x : ℝ≥0) : ℝ)`, `NNReal.toReal e` returns `x`. -/
def isNNRealtoReal (e : Expr) : Option Expr :=
  match e with
  | .app (.const ``NNReal.toReal _) n => some n
  | _ => none

/--
`getNNRealComparisons e` returns a list of all subexpressions of `e` of the form `(x : ℝ)`.
-/
partial def getNNRealCoes (e : Expr) : List Expr :=
  match isNNRealtoReal e with
  | some x => [x]
  | none => match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => getNNRealCoes a ++ getNNRealCoes b
    | (``HMul.hMul, #[_, _, _, _, a, b]) => getNNRealCoes a ++ getNNRealCoes b
    | (``HSub.hSub, #[_, _, _, _, a, b]) => getNNRealCoes a ++ getNNRealCoes b
    | (``Neg.neg, #[_, _, a]) => getNNRealCoes a
    | _ => []

/-- If `e : ℝ≥0`, returns a proof of `0 ≤ (e : ℝ)`. -/
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
    let atoms : List Expr ← withNewMCtxDepth <| AtomM.run .reducible do
      for h in l do
        let (_, _, a, b) ← (← inferType h).ineq?
        discard <| (getNNRealCoes a).mapM AtomM.addAtom
        discard <| (getNNRealCoes b).mapM AtomM.addAtom
      pure (← get).atoms.toList
    let nonneg_pfs : List Expr ← atoms.filterMapM mk_toReal_nonneg_prf
    pure [(g, nonneg_pfs ++ l)]

end  Mathlib.Tactic.Linarith
