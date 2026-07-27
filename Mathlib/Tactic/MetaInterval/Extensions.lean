module

public import Mathlib.Tactic.MetaInterval.Interval
public meta import Mathlib.Tactic.MetaInterval.Certificate
public import Mathlib.Tactic.MetaInterval.Dyadic
public meta import Mathlib.Tactic.MetaInterval.Core
public import Mathlib.Algebra.Order.Field.Basic

set_option linter.style.header false

@[expose] public section

open Lean Meta Elab Tactic

namespace IntervalArithmetic
namespace MetaInterval

/-! ### Arithmetic on intervals -/

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

/-- Multiplication is precise for bounded intervals and conservatively returns `univ` otherwise. -/
def mul (x y : Interval Dyadic) : Interval Dyadic :=
  match x, y with
  | ⟨some xl, some xu⟩, ⟨some yl, some yu⟩ =>
      ⟨some (min4 (xl * yl) (xl * yu) (xu * yl) (xu * yu)),
        some (max4 (xl * yl) (xl * yu) (xu * yl) (xu * yu))⟩
  | _, _ => Interval.univ Dyadic

/-- The number of binary digits used when a reciprocal is not exactly dyadic. -/
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

/-! ### Correctness lemmas -/

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

theorem ofNat_mem (n : ℕ) :
    (OfNat.ofNat n : ℝ) ∈ ((ofNat n).map Dyadic.toReal).toSet := by
  constructor
  · exact WithBot.coe_le_coe.mpr <| by
      simp [Dyadic.toReal, Dyadic.toRat_natCast, Semiring.toGrindSemiring_ofNat ℝ n]
  · exact WithTop.coe_le_coe.mpr <| by
      simp [Dyadic.toReal, Dyadic.toRat_natCast, Semiring.toGrindSemiring_ofNat ℝ n]

theorem add_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ (x.map Dyadic.toReal).toSet) (hsy : s ∈ (y.map Dyadic.toReal).toSet) :
    r + s ∈ ((add x y).map Dyadic.toReal).toSet := by
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

theorem neg_mem {r : ℝ} {x : Interval Dyadic} (hrx : r ∈ (x.map Dyadic.toReal).toSet) :
    -r ∈ ((neg x).map Dyadic.toReal).toSet := by
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
    (hrx : r ∈ (x.map Dyadic.toReal).toSet) (hsy : s ∈ (y.map Dyadic.toReal).toSet) :
    r - s ∈ ((sub x y).map Dyadic.toReal).toSet := by
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
    (hrx : r ∈ (x.map Dyadic.toReal).toSet) (hsy : s ∈ (y.map Dyadic.toReal).toSet) :
    r * s ∈ ((mul x y).map Dyadic.toReal).toSet := by
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
  | ⟨⊥, _⟩, _ | ⟨some _, ⊤⟩, _ | _, ⟨⊥, _⟩ | _, ⟨some _, ⊤⟩ =>
    simp [mul, Interval.univ, Interval.map, Interval.toSet]

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

theorem inv_mem {r : ℝ} {x : Interval Dyadic} (hrx : r ∈ (x.map Dyadic.toReal).toSet) :
    1 / r ∈ ((inv x).map Dyadic.toReal).toSet := by
  match x with
  | ⟨some xl, some xu⟩ =>
    by_cases hsign : 0 < xl ∨ xu < 0
    · have hxlr : Dyadic.toReal xl ≤ r := WithBot.coe_le_coe.mp hrx.1
      have hrxu : r ≤ Dyadic.toReal xu := WithTop.coe_le_coe.mp hrx.2
      simp only [inv, hsign, if_pos, Interval.map]
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
    · simp [inv, hsign, Interval.univ, Interval.map, Interval.toSet]
  | ⟨⊥, _⟩ | ⟨some _, ⊤⟩ => simp [inv, Interval.univ, Interval.map, Interval.toSet]

theorem div_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ (x.map Dyadic.toReal).toSet) (hsy : s ∈ (y.map Dyadic.toReal).toSet) :
    r / s ∈ ((div x y).map Dyadic.toReal).toSet := by
  rw [div_eq_mul_one_div]
  exact mul_mem hrx (inv_mem hsy)

/-! ### Extension implementations -/

meta section

meta def realUnaryArg (e : Expr) : CertificateGeneratorM Expr := do
  let .app _ a ← whnfR e | failure
  unless ← isDefEq (← inferType a) (mkConst ``Real) do failure
  unless ← isDefEq (← inferType e) (mkConst ``Real) do failure
  return a

meta def realBinaryArgs (e : Expr) : CertificateGeneratorM (Expr × Expr) := do
  let .app (.app _ a) b ← whnfR e | failure
  unless ← isDefEq (← inferType a) (mkConst ``Real) do failure
  unless ← isDefEq (← inferType b) (mkConst ``Real) do failure
  unless ← isDefEq (← inferType e) (mkConst ``Real) do failure
  return (a, b)

meta def mapPureUnary (body : CertificateBody) (op inclusion : Name) :
    CertificateGeneratorM CertificateBody := do
  let .pureBody body := body
    | throwError "Pure unary interval extension received a meta certificate"
  let intervalExprBody ← mkAppM op #[body.intervalExprBody]
  let intervalCompBody ← mkAppM op #[body.intervalCompBody]
  let intervalProofBody ← mkAppM inclusion #[body.intervalProofBody]
  return .pureBody ⟨intervalExprBody, intervalCompBody, intervalProofBody⟩

meta def mapPureBinary (left right : CertificateBody) (op inclusion : Name) :
    CertificateGeneratorM CertificateBody := do
  let .pureBody left := left
    | throwError "Pure binary interval extension received a meta left certificate"
  let .pureBody right := right
    | throwError "Pure binary interval extension received a meta right certificate"
  let intervalExprBody ← mkAppM op #[left.intervalExprBody, right.intervalExprBody]
  let intervalCompBody ← mkAppM op #[left.intervalCompBody, right.intervalCompBody]
  let intervalProofBody ←
    mkAppM inclusion #[left.intervalProofBody, right.intervalProofBody]
  return .pureBody ⟨intervalExprBody, intervalCompBody, intervalProofBody⟩

meta def evalPureUnary (e : Expr) (op inclusion : Name) :
    CertificateGeneratorM CertificateBody := do
  let a ← realUnaryArg e
  mapPureUnary (← mkCertificateBody a) op inclusion

meta def evalPureBinary (e : Expr) (op inclusion : Name) :
    CertificateGeneratorM CertificateBody := do
  let (a, b) ← realBinaryArgs e
  let left ← mkCertificateBody a
  let right ← mkCertificateBody b
  mapPureBinary left right op inclusion

@[intervalExt OfNat.ofNat _]
meta def evalOfNat : IntervalExt where
  eval e := do
    let (``OfNat.ofNat, #[α, n, _]) := e.getAppFnArgs | failure
    unless ← isDefEq α (mkConst ``Real) do failure
    guard n.isRawNatLit
    let intervalBody ← mkAppM ``ofNat #[n]
    let proofBody ← mkAppM ``ofNat_mem #[n]
    return .pureBody ⟨intervalBody, intervalBody, proofBody⟩

@[intervalExt Neg.neg _]
meta def evalNeg : IntervalExt where
  eval e := evalPureUnary e ``neg ``neg_mem

@[intervalExt _ + _]
meta def evalAdd : IntervalExt where
  eval e := evalPureBinary e ``add ``add_mem

@[intervalExt _ - _]
meta def evalSub : IntervalExt where
  eval e := evalPureBinary e ``sub ``sub_mem

@[intervalExt _ * _]
meta def evalMul : IntervalExt where
  eval e := evalPureBinary e ``mul ``mul_mem

@[intervalExt _ / _]
meta def evalDiv : IntervalExt where
  eval e := evalPureBinary e ``div ``div_mem

end

end MetaInterval

end IntervalArithmetic
