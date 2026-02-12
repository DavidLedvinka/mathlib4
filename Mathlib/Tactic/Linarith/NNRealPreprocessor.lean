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

initialize nnrealToRealTransform.set fun l => do
  let l ← l.mapM fun e => do
    let t ← whnfR (← instantiateMVars (← inferType e))
    if ← isNNRealProp t then
      let g ← mkFreshExprMVar e
      let (some (e', t'), _) ← Term.TermElabM.run' (run_for g.mvarId! (rifyProof none e t))
        | throwError "rifyProof failed on {e}"
      if ← succeeds t'.ineqOrNotIneq? then
        pure e'
      else
        pure e
    else
      pure e
  let atoms : List Expr ← withNewMCtxDepth <| AtomM.run .reducible do
    for e in l do
      let (_, _, a, b) ← (← inferType e).ineq?
      discard <| (getNNRealCoes a).mapM AtomM.addAtom
      discard <| (getNNRealCoes b).mapM AtomM.addAtom
    return (← get).atoms.toList
  let nonneg_pfs : List Expr ← atoms.filterMapM mk_toReal_nonneg_prf
  return nonneg_pfs ++ l

end  Mathlib.Tactic.Linarith
