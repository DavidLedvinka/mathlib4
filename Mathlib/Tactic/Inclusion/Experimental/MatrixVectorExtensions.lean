module

public import Mathlib.Tactic.Inclusion.Experimental.DyadicRealOperations
public import Mathlib.Tactic.Inclusion.Extension.Extensions
public meta import Mathlib.Tactic.Inclusion.Extension.Extensions
public meta import Mathlib.Tactic.Inclusion.Experimental.Families
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Notation

set_option linter.style.header false

@[expose] public section

set_option warn.sorry false

open Lean Meta Set
open scoped Matrix Matrix.Norms.Elementwise

namespace Inclusion.MatrixVector

variable {m n p : ℕ}

/-- Componentwise dyadic interval bounds for a real vector. -/
structure VectorBox (n : ℕ) where
  bounds : Fin n → Interval Dyadic

/-- Componentwise dyadic interval bounds for a real matrix. -/
structure MatrixBox (m n : ℕ) where
  bounds : Matrix (Fin m) (Fin n) (Interval Dyadic)

def VectorBox.toSet (box : VectorBox n) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i ∈ box.bounds i}

def MatrixBox.toSet (box : MatrixBox m n) : Set (Matrix (Fin m) (Fin n) ℝ) :=
  {A | ∀ i j, A i j ∈ box.bounds i j}

instance : ToSet (VectorBox n) (Fin n → ℝ) := ⟨VectorBox.toSet⟩

instance : ToSet (MatrixBox m n) (Matrix (Fin m) (Fin n) ℝ) := ⟨MatrixBox.toSet⟩

def VectorBox.univ (n : ℕ) : VectorBox n := ⟨fun _ => Interval.univ Dyadic⟩

def MatrixBox.univ (m n : ℕ) : MatrixBox m n := ⟨fun _ _ => Interval.univ Dyadic⟩

instance : Univ (VectorBox n) (Fin n → ℝ) where
  univ := VectorBox.univ n
  mem_univ x i := Inclusion.mem_univ (x i)

instance : Univ (MatrixBox m n) (Matrix (Fin m) (Fin n) ℝ) where
  univ := MatrixBox.univ m n
  mem_univ A i j := Inclusion.mem_univ (A i j)

def VectorBox.refine (x y : VectorBox n) : VectorBox n :=
  ⟨fun i => (x.bounds i).inter (y.bounds i)⟩

def MatrixBox.refine (x y : MatrixBox m n) : MatrixBox m n :=
  ⟨fun i j => (x.bounds i j).inter (y.bounds i j)⟩

theorem VectorBox.refine_mem {x : Fin n → ℝ} {s t : VectorBox n}
    (hs : x ∈ s) (ht : x ∈ t) : x ∈ s.refine t := fun i => inter_mem (hs i) (ht i)

theorem MatrixBox.refine_mem {A : Matrix (Fin m) (Fin n) ℝ} {s t : MatrixBox m n}
    (hs : A ∈ s) (ht : A ∈ t) : A ∈ s.refine t := fun i j => inter_mem (hs i j) (ht i j)

instance : Refine (VectorBox n) (Fin n → ℝ) where
  refine := VectorBox.refine
  mem_refine := VectorBox.refine_mem

instance : Refine (MatrixBox m n) (Matrix (Fin m) (Fin n) ℝ) where
  refine := MatrixBox.refine
  mem_refine := MatrixBox.refine_mem

def sumIntervals {n : ℕ} (f : Fin n → Interval Dyadic) : Interval Dyadic :=
  Fin.foldr n (fun i result => Inclusion.add (f i) result) (Inclusion.ofNat 0)

def VectorBox.zero (n : ℕ) : VectorBox n :=
  ⟨fun _ => Inclusion.ofNat 0⟩

def MatrixBox.zero (m n : ℕ) : MatrixBox m n :=
  ⟨fun _ _ => Inclusion.ofNat 0⟩

def VectorBox.neg (x : VectorBox n) : VectorBox n :=
  ⟨fun i => Inclusion.neg (x.bounds i)⟩

def VectorBox.add (x y : VectorBox n) : VectorBox n :=
  ⟨fun i => Inclusion.add (x.bounds i) (y.bounds i)⟩

def VectorBox.sub (x y : VectorBox n) : VectorBox n :=
  ⟨fun i => Inclusion.sub (x.bounds i) (y.bounds i)⟩

def MatrixBox.neg (x : MatrixBox m n) : MatrixBox m n :=
  ⟨fun i j => Inclusion.neg (x.bounds i j)⟩

def MatrixBox.add (x y : MatrixBox m n) : MatrixBox m n :=
  ⟨fun i j => Inclusion.add (x.bounds i j) (y.bounds i j)⟩

def MatrixBox.sub (x y : MatrixBox m n) : MatrixBox m n :=
  ⟨fun i j => Inclusion.sub (x.bounds i j) (y.bounds i j)⟩

/-- Componentwise interval matrix-vector multiplication. -/
def MatrixBox.mulVec (A : MatrixBox m n) (x : VectorBox n) : VectorBox m :=
  ⟨fun i => sumIntervals fun j =>
    Inclusion.mul (A.bounds i j) (x.bounds j)⟩

/-- Interval matrix multiplication, retaining a box for every output entry. -/
def MatrixBox.mul (A : MatrixBox m n) (B : MatrixBox n p) : MatrixBox m p :=
  ⟨fun i k => sumIntervals fun j =>
    Inclusion.mul (A.bounds i j) (B.bounds j k)⟩

def dyadicAbs (x : Dyadic) : Dyadic := if x < 0 then -x else x

def intervalAbsUpper (x : Interval Dyadic) : WithTop Dyadic :=
  match x.lb, x.ub with
  | some l, some u => some (max (dyadicAbs l) (dyadicAbs u))
  | _, _ => ⊤

/-- A dyadic interval containing the supremum norm of every vector in `x`. -/
def VectorBox.norm (x : VectorBox n) : Interval Dyadic :=
  ⟨some 0, Fin.foldr n (fun i result => max (intervalAbsUpper (x.bounds i)) result) 0⟩

theorem vector_zero_mem (n : ℕ) : (0 : Fin n → ℝ) ∈ VectorBox.zero n := by
  sorry

theorem matrix_zero_mem (m n : ℕ) :
    (0 : Matrix (Fin m) (Fin n) ℝ) ∈ MatrixBox.zero m n := by
  sorry

theorem vector_neg_mem {x : Fin n → ℝ} {s : VectorBox n} (hx : x ∈ s) :
    -x ∈ s.neg := by
  sorry

theorem vector_add_mem {x y : Fin n → ℝ} {s t : VectorBox n}
    (hx : x ∈ s) (hy : y ∈ t) : x + y ∈ s.add t := by
  sorry

theorem vector_sub_mem {x y : Fin n → ℝ} {s t : VectorBox n}
    (hx : x ∈ s) (hy : y ∈ t) : x - y ∈ s.sub t := by
  sorry

theorem matrix_neg_mem {A : Matrix (Fin m) (Fin n) ℝ} {s : MatrixBox m n}
    (hA : A ∈ s) : -A ∈ s.neg := by
  sorry

theorem matrix_add_mem {A B : Matrix (Fin m) (Fin n) ℝ} {s t : MatrixBox m n}
    (hA : A ∈ s) (hB : B ∈ t) : A + B ∈ s.add t := by
  sorry

theorem matrix_sub_mem {A B : Matrix (Fin m) (Fin n) ℝ} {s t : MatrixBox m n}
    (hA : A ∈ s) (hB : B ∈ t) : A - B ∈ s.sub t := by
  sorry

theorem mulVec_mem {A : Matrix (Fin m) (Fin n) ℝ} {x : Fin n → ℝ}
    {s : MatrixBox m n} {t : VectorBox n} (hA : A ∈ s) (hx : x ∈ t) :
    A *ᵥ x ∈ s.mulVec t := by
  sorry

theorem matrix_mul_mem {A : Matrix (Fin m) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin p) ℝ} {s : MatrixBox m n} {t : MatrixBox n p}
    (hA : A ∈ s) (hB : B ∈ t) : A * B ∈ s.mul t := by
  sorry

theorem vector_norm_mem {x : Fin n → ℝ} {s : VectorBox n} (hx : x ∈ s) :
    ‖x‖ ∈ s.norm := by
  sorry

def symmetricRadius (radius : Interval Dyadic) : Interval Dyadic :=
  match radius.ub with
  | some r => ⟨some (-r), some r⟩
  | ⊤ => Interval.univ Dyadic

/-- Expand every coordinate interval by an enclosed metric radius. -/
def VectorBox.closedBallHull (center : VectorBox n) (radius : Interval Dyadic) : VectorBox n :=
  ⟨fun i => Inclusion.add (center.bounds i) (symmetricRadius radius)⟩

/-- Expand every matrix-entry interval by an enclosed metric radius. -/
def MatrixBox.closedBallHull (center : MatrixBox m n) (radius : Interval Dyadic) : MatrixBox m n :=
  ⟨fun i j => Inclusion.add (center.bounds i j) (symmetricRadius radius)⟩

theorem vector_closedBallHull_mem {x center : Fin n → ℝ} {radius : ℝ}
    {centerBox : VectorBox n} {radiusInterval : Interval Dyadic}
    (hcenter : center ∈ centerBox) (hradius : radius ∈ radiusInterval)
    (hx : x ∈ Metric.closedBall center radius) :
    x ∈ centerBox.closedBallHull radiusInterval := by
  sorry

theorem matrix_closedBallHull_mem {A center : Matrix (Fin m) (Fin n) ℝ} {radius : ℝ}
    {centerBox : MatrixBox m n} {radiusInterval : Interval Dyadic}
    (hcenter : center ∈ centerBox) (hradius : radius ∈ radiusInterval)
    (hA : A ∈ Metric.closedBall center radius) :
    A ∈ centerBox.closedBallHull radiusInterval := by
  sorry

meta def finSize? (type : Expr) : MetaM (Option Expr) := do
  let (``Fin, #[n]) := (← whnfR type).getAppFnArgs | return none
  return some n

meta def vectorSize? (type : Expr) : MetaM (Option Expr) := do
  let .forallE _ indexType valueType _ ← whnfR type | return none
  let some n ← finSize? indexType | return none
  unless ← isDefEq valueType (mkConst ``Real) do return none
  return some n

meta def matrixSizes? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← whnfR type
  if let (``Matrix, #[rowType, columnType, valueType]) := type.getAppFnArgs then
    let some m ← finSize? rowType | return none
    let some n ← finSize? columnType | return none
    unless ← isDefEq valueType (mkConst ``Real) do return none
    return some (m, n)
  let .forallE _ rowType columns _ := type | return none
  let .forallE _ columnType valueType _ ← whnfR columns | return none
  let some m ← finSize? rowType | return none
  let some n ← finSize? columnType | return none
  unless ← isDefEq valueType (mkConst ``Real) do return none
  return some (m, n)

meta def lastUnaryArg (e : Expr) : InclusionM Expr := do
  let (_, args) := e.getAppFnArgs
  if h : 0 < args.size then return args[args.size - 1]'(by omega)
  failure

meta def lastBinaryArgs (e : Expr) : InclusionM (Expr × Expr) := do
  let (_, args) := e.getAppFnArgs
  if h : 2 ≤ args.size then
    return (args[args.size - 2]'(by omega), args[args.size - 1]'(by omega))
  failure

meta def evalVectorUnary (e : Expr) (op inclusion : Name) : InclusionM ExprInclusionBody := do
  let x ← lastUnaryArg e
  let some _ ← vectorSize? (← inferType e) | failure
  unless ← isDefEq (← inferType x) (← inferType e) do failure
  let body ← mkExprInclusionBody x
  return ⟨← mkAppM op #[body.inclusionBody], ← mkAppM inclusion #[body.proofBody]⟩

meta def evalMatrixUnary (e : Expr) (op inclusion : Name) : InclusionM ExprInclusionBody := do
  let x ← lastUnaryArg e
  let some _ ← matrixSizes? (← inferType e) | failure
  unless ← isDefEq (← inferType x) (← inferType e) do failure
  let body ← mkExprInclusionBody x
  return ⟨← mkAppM op #[body.inclusionBody], ← mkAppM inclusion #[body.proofBody]⟩

meta def evalVectorBinary (e : Expr) (op inclusion : Name) : InclusionM ExprInclusionBody := do
  let (x, y) ← lastBinaryArgs e
  let some _ ← vectorSize? (← inferType e) | failure
  unless ← isDefEq (← inferType x) (← inferType e) do failure
  unless ← isDefEq (← inferType y) (← inferType e) do failure
  let left ← mkExprInclusionBody x
  let right ← mkExprInclusionBody y
  return ⟨← mkAppM op #[left.inclusionBody, right.inclusionBody],
    ← mkAppM inclusion #[left.proofBody, right.proofBody]⟩

meta def evalMatrixBinary (e : Expr) (op inclusion : Name) : InclusionM ExprInclusionBody := do
  let (x, y) ← lastBinaryArgs e
  let some _ ← matrixSizes? (← inferType e) | failure
  unless ← isDefEq (← inferType x) (← inferType e) do failure
  unless ← isDefEq (← inferType y) (← inferType e) do failure
  let left ← mkExprInclusionBody x
  let right ← mkExprInclusionBody y
  return ⟨← mkAppM op #[left.inclusionBody, right.inclusionBody],
    ← mkAppM inclusion #[left.proofBody, right.proofBody]⟩

meta def evalZeroBody (e : Expr) : InclusionM ExprInclusionBody := do
  if let some n ← vectorSize? (← inferType e) then
    return ⟨← mkAppM ``VectorBox.zero #[n], ← mkAppM ``vector_zero_mem #[n]⟩
  if let some (m, n) ← matrixSizes? (← inferType e) then
    return ⟨← mkAppM ``MatrixBox.zero #[m, n], ← mkAppM ``matrix_zero_mem #[m, n]⟩
  failure

@[inclusionExt matrix.vector | Zero.zero]
meta def evalZero : InclusionExt where
  derive := evalZeroBody

@[inclusionExt matrix.vector | OfNat.ofNat _]
meta def evalOfNatZero : InclusionExt where
  derive e := do
    let (``OfNat.ofNat, #[_, numeral, _]) := e.getAppFnArgs | failure
    guard (numeral.rawNatLit? == some 0)
    evalZeroBody e

@[inclusionExt matrix.vector | Neg.neg _]
meta def evalNeg : InclusionExt where
  derive e :=
    try evalVectorUnary e ``VectorBox.neg ``vector_neg_mem
    catch _ => evalMatrixUnary e ``MatrixBox.neg ``matrix_neg_mem

@[inclusionExt matrix.vector | _ + _]
meta def evalAdd : InclusionExt where
  derive e :=
    try evalVectorBinary e ``VectorBox.add ``vector_add_mem
    catch _ => evalMatrixBinary e ``MatrixBox.add ``matrix_add_mem

@[inclusionExt matrix.vector | _ - _]
meta def evalSub : InclusionExt where
  derive e :=
    try evalVectorBinary e ``VectorBox.sub ``vector_sub_mem
    catch _ => evalMatrixBinary e ``MatrixBox.sub ``matrix_sub_mem

@[inclusionExt matrix.vector | _ * _]
meta def evalMatrixMul : InclusionExt where
  derive e := do
    let (A, B) ← lastBinaryArgs e
    let some (m, n) ← matrixSizes? (← inferType A) | failure
    let some (n', p) ← matrixSizes? (← inferType B) | failure
    let some (m', p') ← matrixSizes? (← inferType e) | failure
    unless ← isDefEq m m' do failure
    unless ← isDefEq n n' do failure
    unless ← isDefEq p p' do failure
    let left ← mkExprInclusionBody A
    let right ← mkExprInclusionBody B
    return ⟨← mkAppM ``MatrixBox.mul #[left.inclusionBody, right.inclusionBody],
      ← mkAppM ``matrix_mul_mem #[left.proofBody, right.proofBody]⟩

@[inclusionExt matrix.vector | Matrix.mulVec _ _]
meta def evalMulVec : InclusionExt where
  derive e := do
    let (A, x) ← lastBinaryArgs e
    let some (m, n) ← matrixSizes? (← inferType A) | failure
    let some n' ← vectorSize? (← inferType x) | failure
    let some m' ← vectorSize? (← inferType e) | failure
    unless ← isDefEq m m' do failure
    unless ← isDefEq n n' do failure
    let matrixBody ← mkExprInclusionBody A
    let vectorBody ← mkExprInclusionBody x
    return ⟨← mkAppM ``MatrixBox.mulVec #[matrixBody.inclusionBody, vectorBody.inclusionBody],
      ← mkAppM ``mulVec_mem #[matrixBody.proofBody, vectorBody.proofBody]⟩

@[inclusionExt matrix.vector | ‖(_ : Fin _ → ℝ)‖]
meta def evalVectorNorm : InclusionExt where
  derive e := do
    let x ← lastUnaryArg e
    let some _ ← vectorSize? (← inferType x) | failure
    unless ← isDefEq (← inferType e) (mkConst ``Real) do failure
    let body ← mkExprInclusionBody x
    return ⟨← mkAppM ``VectorBox.norm #[body.inclusionBody],
      ← mkAppM ``vector_norm_mem #[body.proofBody]⟩

@[inclusionExt matrix.vector | (_ : Fin _ → ℝ)]
meta def evalVectorIVar : InclusionExt :=
  mkIVarExt fun elemType => do
    let some n ← vectorSize? elemType | failure
    mkAppM ``VectorBox #[n]

@[inclusionExt matrix.vector | (_ : Matrix (Fin _) (Fin _) ℝ)]
meta def evalMatrixIVar : InclusionExt :=
  mkIVarExt fun elemType => do
    let some (m, n) ← matrixSizes? elemType | failure
    mkAppM ``MatrixBox #[m, n]

meta def closedBallArgs? (type : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let (``Membership.mem, #[_, _, _, set, x]) := (← whnfR type).getAppFnArgs | return none
  let (``Metric.closedBall, args) := set.getAppFnArgs | return none
  if args.size < 2 then return none
  return some (x, args[args.size - 2]!, args[args.size - 1]!)

meta def deriveClosedBallHyp (h type : Expr) : HypothesisM Unit := do
  let some (x, center, radius) ← closedBallArgs? type | failure
  let some iExpr ← requestedIVar? x | return
  let (hull, hullMem) ←
    match iExpr.iType.setType.getAppFnArgs with
    | (``VectorBox, #[_]) => pure (``VectorBox.closedBallHull, ``vector_closedBallHull_mem)
    | (``MatrixBox, #[_, _]) => pure (``MatrixBox.closedBallHull, ``matrix_closedBallHull_mem)
    | _ => failure
  let centerBody ← mkHypInclusionBody center iExpr.iType
  let radiusSetType ← mkAppM ``Interval #[mkConst ``Dyadic]
  let radiusToSet ← synthInstance
    (← mkAppM ``ToSet #[radiusSetType, mkConst ``Real])
  let radiusType : IType := ⟨mkConst ``Real, radiusSetType, radiusToSet⟩
  let radiusBody ← mkHypInclusionBody radius radiusType
  let set ← mkAppM hull #[centerBody.inclusionBody, radiusBody.inclusionBody]
  let proof ← mkAppM hullMem #[centerBody.proofBody, radiusBody.proofBody, h]
  addInclusionHyp iExpr ⟨set, proof⟩

@[hypothesisExt matrix.vector | _ ∈ Metric.closedBall _ _]
meta def evalClosedBallHyp : HypothesisExt where
  derive := deriveClosedBallHyp

end Inclusion.MatrixVector
