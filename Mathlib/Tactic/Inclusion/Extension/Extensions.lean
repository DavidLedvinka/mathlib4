module

public import Mathlib.Tactic.Inclusion.Extension.Interval
public import Mathlib.Tactic.Inclusion.Extension.Dyadic
public meta import Mathlib.Tactic.Inclusion.Core.Core
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public meta import Mathlib.Tactic.FunProp

set_option linter.style.header false

@[expose] public section

open Lean Meta
open Set MeasureTheory

namespace IntervalArithmetic.Inclusion

instance instToSetIntervalDyadicReal : ToSet (Interval Dyadic) ℝ where
  toSet I := (I.map Dyadic.toReal).toSet

def ofNat (n : ℕ) : Interval Dyadic := Interval.singleton Dyadic n

def add (x y : Interval Dyadic) : Interval Dyadic where
  lb := match x.lb, y.lb with
    | some a, some b => some (a + b)
    | _, _ => ⊥
  ub := match x.ub, y.ub with
    | some a, some b => some (a + b)
    | _, _ => ⊤

def neg (x : Interval Dyadic) : Interval Dyadic where
  lb := match x.ub with
    | some a => some (-a)
    | ⊤ => ⊥
  ub := match x.lb with
    | some a => some (-a)
    | ⊥ => ⊤

def sub (x y : Interval Dyadic) : Interval Dyadic where
  lb := match x.lb, y.ub with
    | some a, some b => some (a - b)
    | _, _ => ⊥
  ub := match x.ub, y.lb with
    | some a, some b => some (a - b)
    | _, _ => ⊤

def min4 (a b c d : Dyadic) : Dyadic := min (min a b) (min c d)

def max4 (a b c d : Dyadic) : Dyadic := max (max a b) (max c d)

def mul (x y : Interval Dyadic) : Interval Dyadic :=
  match x, y with
  | ⟨some xl, some xu⟩, ⟨some yl, some yu⟩ =>
      ⟨some (min4 (xl * yl) (xl * yu) (xu * yl) (xu * yu)),
        some (max4 (xl * yl) (xl * yu) (xu * yl) (xu * yu))⟩
  | _, _ => Interval.univ Dyadic

def divisionPrecision : Int := 20

def lowerApprox (q : ℚ) : Dyadic := q.toDyadic divisionPrecision

def upperApprox (q : ℚ) : Dyadic :=
  let d := lowerApprox q
  if d.toRat = q then d else d + Dyadic.ofIntWithPrec 1 divisionPrecision

def inv (x : Interval Dyadic) : Interval Dyadic :=
  match x with
  | ⟨some xl, some xu⟩ =>
      if 0 < xl ∨ xu < 0 then
        ⟨some (lowerApprox (1 / xu.toRat)), some (upperApprox (1 / xl.toRat))⟩
      else
        Interval.univ Dyadic
  | _ => Interval.univ Dyadic

def div (x y : Interval Dyadic) : Interval Dyadic := mul x (inv y)

def le (x y : Interval Dyadic) : IntervalBool :=
  match x.ub, y.lb with
  | some xu, some yl => if xu ≤ yl then .true else .undetermined
  | _, _ => .undetermined

theorem mem_univ (r : ℝ) : r ∈ Interval.univ Dyadic := by
  constructor <;> simp [Interval.univ, Interval.map]

@[simp]
lemma toReal_add (a b : Dyadic) :
    Dyadic.toReal (a + b) = Dyadic.toReal a + Dyadic.toReal b := by
  simp [Dyadic.toReal, Dyadic.toRat_add]

@[simp]
lemma toReal_neg (a : Dyadic) : Dyadic.toReal (-a) = -Dyadic.toReal a := by
  simp [Dyadic.toReal, Dyadic.toRat_neg]

@[simp]
lemma toReal_sub (a b : Dyadic) :
    Dyadic.toReal (a - b) = Dyadic.toReal a - Dyadic.toReal b := by
  simp [Dyadic.toReal, Dyadic.toRat_sub]

@[simp]
lemma toReal_mul (a b : Dyadic) :
    Dyadic.toReal (a * b) = Dyadic.toReal a * Dyadic.toReal b := by
  simp [Dyadic.toReal, Dyadic.toRat_mul]

@[simp]
lemma toReal_zero : Dyadic.toReal 0 = 0 := by
  simp [Dyadic.toReal]

lemma toReal_le_toReal {a b : Dyadic} : Dyadic.toReal a ≤ Dyadic.toReal b ↔ a ≤ b := by
  simp [Dyadic.toReal]

lemma toReal_lt_toReal {a b : Dyadic} : Dyadic.toReal a < Dyadic.toReal b ↔ a < b := by
  simp [Dyadic.toReal]

@[simp]
lemma toReal_min (a b : Dyadic) :
    Dyadic.toReal (min a b) = min (Dyadic.toReal a) (Dyadic.toReal b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (toReal_le_toReal.mpr h)]
  · rw [min_eq_right h, min_eq_right (toReal_le_toReal.mpr h)]

@[simp]
lemma toReal_max (a b : Dyadic) :
    Dyadic.toReal (max a b) = max (Dyadic.toReal a) (Dyadic.toReal b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (toReal_le_toReal.mpr h)]
  · rw [max_eq_left h, max_eq_left (toReal_le_toReal.mpr h)]

lemma min4_mul_le {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  have ha : min (a * c) (a * d) ≤ a * y := by
    rcases le_total 0 a with ha | ha
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 ha)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 ha)
  have hb : min (b * c) (b * d) ≤ b * y := by
    rcases le_total 0 b with hb | hb
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 hb)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 hb)
  apply (min_le_min ha hb).trans
  rcases le_total 0 y with hy | hy
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hy)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hy)

lemma mul_le_max4 {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have ha : a * y ≤ max (a * c) (a * d) := by
    rcases le_total 0 a with ha | ha
    · exact (mul_le_mul_of_nonneg_left hy.2 ha).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hy.1 ha).trans (le_max_left _ _)
  have hb : b * y ≤ max (b * c) (b * d) := by
    rcases le_total 0 b with hb | hb
    · exact (mul_le_mul_of_nonneg_left hy.2 hb).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hy.1 hb).trans (le_max_left _ _)
  apply (show x * y ≤ max (a * y) (b * y) by
    rcases le_total 0 y with hy | hy
    · exact (mul_le_mul_of_nonneg_right hx.2 hy).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hx.1 hy).trans (le_max_left _ _)).trans
  exact max_le_max ha hb

theorem ofNat_mem (n : ℕ) : (OfNat.ofNat n : ℝ) ∈ ofNat n := by
  constructor
  · exact WithBot.coe_le_coe.mpr <| by
      simp [Dyadic.toReal, Dyadic.toRat_natCast, Semiring.toGrindSemiring_ofNat ℝ n]
  · exact WithTop.coe_le_coe.mpr <| by
      simp [Dyadic.toReal, Dyadic.toRat_natCast, Semiring.toGrindSemiring_ofNat ℝ n]

theorem add_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x) (hsy : s ∈ y) : r + s ∈ add x y := by
  match x, y with
  | ⟨xl, xu⟩, ⟨yl, yu⟩ =>
    constructor
    · match xl, yl with
      | ⊥, _ | _, ⊥ => simp [add, Interval.map]
      | some a, some b =>
        exact WithBot.coe_le_coe.mpr <| by
          rw [toReal_add]
          exact add_le_add (WithBot.coe_le_coe.mp hrx.1) (WithBot.coe_le_coe.mp hsy.1)
    · match xu, yu with
      | ⊤, _ | _, ⊤ => simp [add, Interval.map]
      | some a, some b =>
        exact WithTop.coe_le_coe.mpr <| by
          rw [toReal_add]
          exact add_le_add (WithTop.coe_le_coe.mp hrx.2) (WithTop.coe_le_coe.mp hsy.2)

theorem neg_mem {r : ℝ} {x : Interval Dyadic} (hrx : r ∈ x) : -r ∈ neg x := by
  match x with
  | ⟨xl, xu⟩ =>
    constructor
    · match xu with
      | ⊤ => simp [neg, Interval.map]
      | some a =>
        exact WithBot.coe_le_coe.mpr <| by
          rw [toReal_neg]
          exact neg_le_neg (WithTop.coe_le_coe.mp hrx.2)
    · match xl with
      | ⊥ => simp [neg, Interval.map]
      | some a =>
        exact WithTop.coe_le_coe.mpr <| by
          rw [toReal_neg]
          exact neg_le_neg (WithBot.coe_le_coe.mp hrx.1)

theorem sub_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x) (hsy : s ∈ y) : r - s ∈ sub x y := by
  match x, y with
  | ⟨xl, xu⟩, ⟨yl, yu⟩ =>
    constructor
    · match xl, yu with
      | ⊥, _ | _, ⊤ => simp [sub, Interval.map]
      | some a, some b =>
        exact WithBot.coe_le_coe.mpr <| by
          rw [toReal_sub]
          exact sub_le_sub (WithBot.coe_le_coe.mp hrx.1) (WithTop.coe_le_coe.mp hsy.2)
    · match xu, yl with
      | ⊤, _ | _, ⊥ => simp [sub, Interval.map]
      | some a, some b =>
        exact WithTop.coe_le_coe.mpr <| by
          rw [toReal_sub]
          exact sub_le_sub (WithTop.coe_le_coe.mp hrx.2) (WithBot.coe_le_coe.mp hsy.1)

theorem mul_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x) (hsy : s ∈ y) : r * s ∈ mul x y := by
  match x, y with
  | ⟨some xl, some xu⟩, ⟨some yl, some yu⟩ =>
    have hx : Dyadic.toReal xl ≤ r ∧ r ≤ Dyadic.toReal xu :=
      ⟨WithBot.coe_le_coe.mp hrx.1, WithTop.coe_le_coe.mp hrx.2⟩
    have hy : Dyadic.toReal yl ≤ s ∧ s ≤ Dyadic.toReal yu :=
      ⟨WithBot.coe_le_coe.mp hsy.1, WithTop.coe_le_coe.mp hsy.2⟩
    constructor
    · exact WithBot.coe_le_coe.mpr <| by
        simpa [min4] using min4_mul_le hx hy
    · exact WithTop.coe_le_coe.mpr <| by
        simpa [max4] using mul_le_max4 hx hy
  | ⟨⊥, _⟩, _ | ⟨some _, ⊤⟩, _ | ⟨some _, some _⟩, ⟨⊥, _⟩
    | ⟨some _, some _⟩, ⟨some _, ⊤⟩ =>
    exact mem_univ _

lemma lowerApprox_le (q : ℚ) : Dyadic.toReal (lowerApprox q) ≤ (q : ℝ) := by
  exact Rat.cast_le.mpr Rat.toRat_toDyadic_le

lemma le_upperApprox (q : ℚ) : (q : ℝ) ≤ Dyadic.toReal (upperApprox q) := by
  simp only [upperApprox]
  split_ifs with h
  · rw [Dyadic.toReal]
    exact Rat.cast_le.mpr h.symm.le
  · rw [Dyadic.toReal, Dyadic.toRat_add]
    exact Rat.cast_le.mpr
      (by simpa [lowerApprox] using
        (Rat.lt_toRat_toDyadic_add (x := q) (prec := divisionPrecision)).le)

theorem inv_mem {r : ℝ} {x : Interval Dyadic} (hrx : r ∈ x) : 1 / r ∈ inv x := by
  match x with
  | ⟨some xl, some xu⟩ =>
    by_cases hsign : 0 < xl ∨ xu < 0
    · have hxlr : Dyadic.toReal xl ≤ r := WithBot.coe_le_coe.mp hrx.1
      have hrxu : r ≤ Dyadic.toReal xu := WithTop.coe_le_coe.mp hrx.2
      simp only [inv, hsign, if_pos]
      constructor
      · apply WithBot.coe_le_coe.mpr
        apply (lowerApprox_le (1 / xu.toRat)).trans
        rw [Rat.cast_div, Rat.cast_one]
        rcases hsign with hxl | hxu
        · have hxl' : 0 < Dyadic.toReal xl := by
            simpa using toReal_lt_toReal.mpr hxl
          exact one_div_le_one_div_of_le (hxl'.trans_le hxlr) hrxu
        · have hxu' : Dyadic.toReal xu < 0 := by
            simpa using toReal_lt_toReal.mpr hxu
          exact one_div_le_one_div_of_neg_of_le hxu' hrxu
      · apply WithTop.coe_le_coe.mpr
        apply (show 1 / r ≤ (1 / xl.toRat : ℚ) from ?_).trans (le_upperApprox _)
        rw [Rat.cast_div, Rat.cast_one]
        rcases hsign with hxl | hxu
        · have hxl' : 0 < Dyadic.toReal xl := by
            simpa using toReal_lt_toReal.mpr hxl
          exact one_div_le_one_div_of_le hxl' hxlr
        · have hxu' : Dyadic.toReal xu < 0 := by
            simpa using toReal_lt_toReal.mpr hxu
          exact one_div_le_one_div_of_neg_of_le (hrxu.trans_lt hxu') hxlr
    · simpa [inv, hsign] using mem_univ (1 / r)
  | ⟨⊥, _⟩ | ⟨some _, ⊤⟩ => simpa [inv] using mem_univ (1 / r)

theorem div_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x) (hsy : s ∈ y) : r / s ∈ div x y := by
  rw [div_eq_mul_one_div]
  exact mul_mem hrx (inv_mem hsy)

theorem mem_intervalBool_true {p : Prop} (hp : p) : p ∈ IntervalBool.true := by
  simpa [ToSet.toSet, IntervalBool.toPropSet] using hp

theorem mem_intervalBool_undetermined (p : Prop) : p ∈ IntervalBool.undetermined := by
  classical
  by_cases hp : p <;> simp [ToSet.toSet, IntervalBool.toPropSet, hp]

theorem le_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x) (hsy : s ∈ y) : (r ≤ s) ∈ le x y := by
  match x, y with
  | ⟨_, some xu⟩, ⟨some yl, _⟩ =>
    simp only [le]
    split_ifs with h
    · apply mem_intervalBool_true
      exact (WithTop.coe_le_coe.mp hrx.2).trans
        ((Monotone.dyadicToReal h).trans (WithBot.coe_le_coe.mp hsy.1))
    · exact mem_intervalBool_undetermined _
  | ⟨_, ⊤⟩, _ | ⟨_, some _⟩, ⟨⊥, _⟩ => exact mem_intervalBool_undetermined _

def sumRangeIntervals : ℕ → (ℕ → Interval Dyadic) → Interval Dyadic
  | 0, _ => ofNat 0
  | n + 1, f => add (sumRangeIntervals n f) (f n)

theorem sumRangeIntervals_mem (n : ℕ) {f : ℕ → ℝ} {I : ℕ → Interval Dyadic}
    (h : ∀ i, f i ∈ I i) : Finset.sum (Finset.range n) f ∈ sumRangeIntervals n I := by
  induction n with
  | zero => simpa [sumRangeIntervals] using ofNat_mem 0
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact add_mem ih (h n)

def unitIntegralStep : Dyadic := Dyadic.ofIntWithPrec 1 2

def unitIntegralPoint (i : ℕ) : Dyadic := Dyadic.ofIntWithPrec i 2

def unitIntegralPiece (i : ℕ) : Interval Dyadic :=
  ⟨unitIntegralPoint i, unitIntegralPoint (i + 1)⟩

def unitIntegralBound (g : Interval Dyadic → Interval Dyadic) : Interval Dyadic :=
  sumRangeIntervals 4 fun i =>
    mul (Interval.singleton Dyadic unitIntegralStep) (g (unitIntegralPiece i))

@[simp]
theorem unitIntegralPoint_toReal (i : ℕ) :
    Dyadic.toReal (unitIntegralPoint i) = (i : ℝ) / 4 := by
  norm_num [unitIntegralPoint, Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  ring

@[simp]
theorem unitIntegralStep_toReal : Dyadic.toReal unitIntegralStep = (1 : ℝ) / 4 := by
  norm_num [unitIntegralStep, Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]

theorem integralPiece_mem {a b : ℝ} {f : ℝ → ℝ} {w : Dyadic} {I : Interval Dyadic}
    (hab : a ≤ b) (hw : b - a = Dyadic.toReal w)
    (hf : IntervalIntegrable f volume a b) (h : ∀ x ∈ Icc a b, f x ∈ I) :
    (∫ x in a..b, f x) ∈ mul (Interval.singleton Dyadic w) I := by
  match I with
  | ⟨some l, some u⟩ =>
    have hl : ∫ _ in a..b, Dyadic.toReal l ≤ ∫ x in a..b, f x := by
      apply intervalIntegral.integral_mono_on hab
        (Continuous.intervalIntegrable continuous_const _ _) hf
      intro x hx
      exact WithBot.coe_le_coe.mp (h x hx).1
    have hu : ∫ x in a..b, f x ≤ ∫ _ in a..b, Dyadic.toReal u := by
      apply intervalIntegral.integral_mono_on hab hf
        (Continuous.intervalIntegrable continuous_const _ _)
      intro x hx
      exact WithTop.coe_le_coe.mp (h x hx).2
    rw [intervalIntegral.integral_const, hw] at hl hu
    constructor
    · apply WithBot.coe_le_coe.mpr
      simpa [mul, Interval.singleton, min4] using
        (min_le_left (Dyadic.toReal w * Dyadic.toReal l)
          (Dyadic.toReal w * Dyadic.toReal u)).trans hl
    · apply WithTop.coe_le_coe.mpr
      simpa [mul, Interval.singleton, max4] using
        hu.trans (le_max_right (Dyadic.toReal w * Dyadic.toReal l)
          (Dyadic.toReal w * Dyadic.toReal u))
  | ⟨⊥, _⟩ | ⟨some _, ⊤⟩ =>
    exact mem_univ _

theorem unitIntegral_mem {f : ℝ → ℝ}
    (g : Interval Dyadic → Interval Dyadic) (hf : Continuous f)
    (h : ∀ (x : ℝ) (I : Interval Dyadic), x ∈ I → f x ∈ g I) :
    (∫ x in (0 : ℝ)..1, f x) ∈ unitIntegralBound g := by
  have hpiece (i : ℕ) :
      (∫ x in Dyadic.toReal (unitIntegralPoint i)..
        Dyadic.toReal (unitIntegralPoint (i + 1)), f x) ∈
        mul (Interval.singleton Dyadic unitIntegralStep) (g (unitIntegralPiece i)) := by
    apply integralPiece_mem
    · simp only [unitIntegralPoint_toReal, Nat.cast_add, Nat.cast_one]
      linarith
    · simp [unitIntegralPoint_toReal, unitIntegralStep_toReal]
      ring
    · exact hf.intervalIntegrable _ _
    · intro x hx
      apply h x (unitIntegralPiece i)
      exact ⟨WithBot.coe_le_coe.mpr hx.1, WithTop.coe_le_coe.mpr hx.2⟩
  have hsum := sumRangeIntervals_mem 4 hpiece
  have hpartition :=
    intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun i => Dyadic.toReal (unitIntegralPoint i)) (μ := volume) (m := 0) (n := 4)
      (by omega) (fun _ _ => hf.intervalIntegrable _ _)
  have hpartition' :
      (∑ i ∈ Finset.range 4,
        ∫ x in Dyadic.toReal (unitIntegralPoint i)..
          Dyadic.toReal (unitIntegralPoint (i + 1)), f x) =
        ∫ x in (0 : ℝ)..1, f x := by
    simpa using hpartition
  rw [← hpartition']
  simpa [unitIntegralBound] using hsum

meta def proveContinuousWithIVars (x integrand : Expr) (ambientIVars : Array Expr) : MetaM Expr :=
  withLocalDeclsD
      (ambientIVars.map fun expr => (`ambient, fun _ => inferType expr)) fun ambientVars => do
    let replacements := (ambientIVars.zip ambientVars).foldl
      (init := ({} : ExprMap Expr)) fun result (old, new) => result.insert old new
    let integrand := integrand.replace fun subterm => replacements[subterm]?
    let integrandFn ← mkLambdaFVars #[x] integrand
    let continuousGoal ← mkAppM ``Continuous #[integrandFn]
    let some proof ←
      Mathlib.Meta.FunProp.tacticToDischarge (← `(tactic| fun_prop)) continuousGoal
      | throwError "fun_prop could not prove {continuousGoal}"
    let proofFn ← mkLambdaFVars ambientVars proof
    return mkAppN proofFn ambientIVars

meta def realUnaryArg (e : Expr) : InclusionM Expr := do
  let .app _ a ← whnfR e | failure
  unless ← isDefEq (← inferType a) (mkConst ``Real) do failure
  unless ← isDefEq (← inferType e) (mkConst ``Real) do failure
  return a

meta def realBinaryArgs (e : Expr) : InclusionM (Expr × Expr) := do
  let .app (.app _ a) b ← whnfR e | failure
  unless ← isDefEq (← inferType a) (mkConst ``Real) do failure
  unless ← isDefEq (← inferType b) (mkConst ``Real) do failure
  unless ← isDefEq (← inferType e) (mkConst ``Real) do failure
  return (a, b)

meta def evalUnary (e : Expr) (op inclusion : Name) : InclusionM ExprInclusionBody := do
  let body ← mkExprInclusionBody (← realUnaryArg e)
  return ⟨← mkAppM op #[body.inclusionBody], ← mkAppM inclusion #[body.proofBody]⟩

meta def evalBinary (e : Expr) (op inclusion : Name) : InclusionM ExprInclusionBody := do
  let (a, b) ← realBinaryArgs e
  let left ← mkExprInclusionBody a
  let right ← mkExprInclusionBody b
  return ⟨← mkAppM op #[left.inclusionBody, right.inclusionBody],
    ← mkAppM inclusion #[left.proofBody, right.proofBody]⟩

@[inclusionExt OfNat.ofNat _]
meta def evalOfNat : InclusionExt where
  eval e := do
    let (``OfNat.ofNat, #[α, n, _]) := e.getAppFnArgs | failure
    unless ← isDefEq α (mkConst ``Real) do failure
    guard n.isRawNatLit
    return ⟨← mkAppM ``ofNat #[n], ← mkAppM ``ofNat_mem #[n]⟩

@[inclusionExt Neg.neg _]
meta def evalNeg : InclusionExt where
  eval e := evalUnary e ``neg ``neg_mem

@[inclusionExt _ + _]
meta def evalAdd : InclusionExt where
  eval e := evalBinary e ``add ``add_mem

@[inclusionExt _ - _]
meta def evalSub : InclusionExt where
  eval e := evalBinary e ``sub ``sub_mem

@[inclusionExt _ * _]
meta def evalMul : InclusionExt where
  eval e := evalBinary e ``mul ``mul_mem

@[inclusionExt _ / _]
meta def evalDiv : InclusionExt where
  eval e := evalBinary e ``div ``div_mem

@[inclusionExt(_ : ℝ) ≤ (_ : ℝ)]
meta def evalLe : InclusionExt where
  eval e := do
    let (``LE.le, #[_, _, a, b]) := e.getAppFnArgs | failure
    unless ← isDefEq (← inferType a) (mkConst ``Real) do failure
    unless ← isDefEq (← inferType b) (mkConst ``Real) do failure
    unless ← isProp e do failure
    let left ← mkExprInclusionBody a
    let right ← mkExprInclusionBody b
    return ⟨← mkAppM ``le #[left.inclusionBody, right.inclusionBody],
      ← mkAppM ``le_mem #[left.proofBody, right.proofBody]⟩

@[inclusionExt intervalIntegral (_ : ℝ → ℝ) _ _ volume]
meta def evalUnitIntegral : InclusionExt where
  eval e := do
    let (``intervalIntegral, #[E, _, _, f, a, b, _]) := e.getAppFnArgs | failure
    unless ← isDefEq E (mkConst ``Real) do failure
    let some (0, _) ← getOfNatValue? a ``Real | failure
    let some (1, _) ← getOfNatValue? b ``Real | failure
    lambdaTelescope f fun xs integrand => do
      let #[x] := xs | failure
      let xType ← inferType x
      let setType ← mkAppM ``Interval #[mkConst ``Dyadic]
      let toSetInst ← synthInstance (← mkAppM ``ToSet #[setType, xType])
      withLocalDeclD `integralInterval setType fun interval => do
        let hypType ← mkToSetMem xType setType x interval toSetInst
        withLocalDeclD `integralHyp hypType fun hyp => do
          let data : IVarData := ⟨⟨xType, setType, toSetInst⟩, x, interval, hyp⟩
          modify fun state => { state with ivars := state.ivars.insert x data }
          let body ← try mkExprInclusionBody integrand finally
            modify fun state => { state with ivars := state.ivars.erase x }
          let ambientIVars := (← get).ivars.toArray.map fun (_, data) => data.exprVar
          let some (genericIntegrand, _, _) := toSetHyp? (← inferType body.proofBody)
            | throwError "The integrand proof is not a containment proof"
          let continuousProof ← proveContinuousWithIVars x genericIntegrand ambientIVars
          let intervalFn ← mkLambdaFVars #[interval] body.inclusionBody
          let proofFn ← mkLambdaFVars #[x, interval, hyp] body.proofBody
          return ⟨← mkAppM ``unitIntegralBound #[intervalFn],
            ← mkAppM ``unitIntegral_mem #[intervalFn, continuousProof, proofFn]⟩

@[inclusionExt(_ : ℝ)]
meta def evalRealIVar : InclusionExt where
  priority := eval_prio high
  eval e := do
    unless ← isDefEq (← inferType e) (mkConst ``Real) do failure
    let setType ← mkAppM ``Interval #[mkConst ``Dyadic]
    let toSetInst ← synthInstance (← mkAppM ``ToSet #[setType, mkConst ``Real])
    return (← mkIVar e setType toSetInst).toExprInclusionBody

end IntervalArithmetic.Inclusion
