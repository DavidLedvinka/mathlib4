module

public import Mathlib.Control.Random
public import Mathlib.MeasureTheory.Measure.GiryMonad

set_option linter.style.header false

@[expose] public section

open Function

section MeasurableSpaceMonad

universe u v

class MeasurableSpaceBind (m : (α : Type u) → [MeasurableSpace α] → Type v) where
  /-- # TODO -/
  mBind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β] :
    m α → (α → m β) → m β

class MeasurableSpacePure (f : (α : Type u) → [MeasurableSpace α] → Type v) where
  mPure {α : Type u} [σα : MeasurableSpace α] : α → f α

class MeasurableSpaceFunctor (f : (α : Type u) → [MeasurableSpace α] → Type v) :
    Type (max (u+1) v) where
  /-- # TODO -/
  mMap {α β : Type u} [σα : MeasurableSpace α] [σβ : MeasurableSpace β] :
    (α → β) → f α → f β
  mMapConst {α β : Type u} [mα : MeasurableSpace α] [mβ : MeasurableSpace β] :
    α → f β → f α := Function.comp mMap (const _)

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

class MeasurableSpaceMonad (m : (α : Type u) → [MeasurableSpace α] → Type v) :
    Type (max (u+1) v)
    extends MeasurableSpaceFunctor m, MeasurableSpacePure m, MeasurableSpaceBind m where
  mMap f μ := mBind μ (Function.comp mPure f)

@[inherit_doc] infixr:100 " <$>ₘ " => MeasurableSpaceFunctor.mMap
@[inherit_doc] infixl:55  " >>=ₘ " => MeasurableSpaceBind.mBind

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} {α β : Type u}
  [MeasurableSpace α] [MeasurableSpace β]

theorem MeasurableSpaceBind.bind_congr [MeasurableSpaceBind m] {x : m α} {f g : α → m β}
    (h : ∀ a, f a = g a) : x >>=ₘ f = x >>=ₘ g := by
  simp [funext h]

theorem MeasurableSpaceFunctor.map_congr [MeasurableSpaceFunctor m] {x : m α} {f g : α → β}
    (h : ∀ a, f a = g a) : (f <$>ₘ x : m β) = g <$>ₘ x := by
  simp [funext h]

end MeasurableSpaceMonad

section Lawful

universe u v

open MeasurableSpaceFunctor

class LawfulMeasurableSpaceFunctor
    (f : (α : Type u) → [MeasurableSpace α] → Type v) [MeasurableSpaceFunctor f]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (f α)] : Prop where
  mMap_measurable {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
      {g : α → β} (hg : Measurable g) :
    Measurable (mMap (f := f) g)
  mMap_const {α β : Type u} [MeasurableSpace α] [MeasurableSpace β] :
    (mMapConst : α → f β → f α) = mMap ∘ Function.const β
  id_mMap {α : Type u} [MeasurableSpace α] (x : f α) :
    id <$>ₘ x = x
  comp_mMap {α β γ : Type u}
      [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
      {g : α → β} {h : β → γ} (x : f α) (g_meas : Measurable g) (h_meas : Measurable h) :
    (h ∘ g) <$>ₘ x = h <$>ₘ g <$>ₘ x

open LawfulMeasurableSpaceFunctor

attribute [fun_prop] mMap_measurable
attribute [simp] id_mMap

variable {f : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceFunctor f]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (f α)] [LawfulMeasurableSpaceFunctor f]
  {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

@[simp] theorem id_mMap' (x : f α) : (fun a => a) <$>ₘ x = x := id_mMap x

@[simp] theorem mMap_mMap {m : α → β} {g : β → γ} (x : f α)
    (hm : Measurable m) (hg : Measurable g) : g <$>ₘ m <$>ₘ x = (fun a => g (m a)) <$>ₘ x :=
  (comp_mMap x hm hg).symm

theorem mMap_measurable' {g : α → β} (hg : Measurable g) : Measurable (fun x : f α => g <$>ₘ x) :=
  mMap_measurable hg

@[simp] theorem mMap_unit {a : f PUnit} : (fun _ => PUnit.unit) <$>ₘ a = a := by
  simp

open MeasurableSpaceBind MeasurableSpacePure MeasurableSpaceFunctor

class LawfulMeasurableSpaceMonad
    (m : (α : Type u) → [MeasurableSpace α] → Type v) [MeasurableSpaceMonad m]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)] : Prop
    extends LawfulMeasurableSpaceFunctor m where
  mPure_measurable {α : Type u} [MeasurableSpace α] :
    Measurable (mPure : α → m α)
  mBind_measurable {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
      {f : α → m β} (hf : Measurable f) :
    Measurable (fun x : m α => x >>=ₘ f)
  mBind_mPure_comp {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
      {f : α → β} (hf : Measurable f) (x : m α) :
    x >>=ₘ (fun a => mPure (f a)) = f <$>ₘ x
  mPure_mBind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
      (x : α) {f : α → m β} (hf : Measurable f) :
    mPure x >>=ₘ f = f x
  mBind_assoc {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
      (x : m α) {f : α → m β} {g : β → m γ} (hf : Measurable f) (hg : Measurable g) :
    x >>=ₘ f >>=ₘ g = x >>=ₘ fun x => f x >>=ₘ g
  mMap_measurable hg := (by
    convert mBind_measurable (mPure_measurable.comp hg)
    exact (mBind_mPure_comp hg _).symm)
  comp_mMap x g_meas h_meas := (by
    rw [← mBind_mPure_comp (by fun_prop), ← mBind_mPure_comp h_meas,
      ← mBind_mPure_comp g_meas, mBind_assoc _ (by fun_prop) (by fun_prop)]
    congr with _
    exact (mPure_mBind _ (mPure_measurable.comp h_meas)).symm)

open LawfulMeasurableSpaceMonad

attribute [fun_prop] mPure_measurable mBind_measurable
attribute [simp] pure_bind bind_assoc bind_pure_comp
attribute [grind <=] pure_bind

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)] [LawfulMeasurableSpaceMonad m]
  {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

@[simp] theorem mMap_mPure {f : α → β} (hf : Measurable f) (x : α) :
    f <$>ₘ (mPure x : m α) = mPure (f x) := by
  rw [← mBind_mPure_comp hf, mPure_mBind _ (by fun_prop)]

@[simp] theorem mBind_mPure (x : m α) :
    x >>=ₘ mPure = x := by
  change x >>=ₘ (fun a => (mPure (id a))) = x
  rw [mBind_mPure_comp (by fun_prop), id_mMap]

theorem mMap_eq_mPure_mBind {f : α → β} (hf : Measurable f) (x : m α) :
    f <$>ₘ x = x >>=ₘ fun a => mPure (f a) := by
  rw [← mBind_mPure_comp hf x]

theorem mBind_mPure_unit {x : m PUnit} :
    (x >>=ₘ fun _ => mPure ⟨⟩) = x := by
  rw [mBind_mPure]

@[simp] theorem mMap_mBind {f : β → γ} (hf : Measurable f) (x : m α)
      {g : α → m β} (hg : Measurable g) :
    f <$>ₘ (x >>=ₘ g) = x >>=ₘ fun a => f <$>ₘ g a := by
  rw [← mBind_mPure_comp hf, mBind_assoc _ hg (by fun_prop)]
  simp (disch := fun_prop) [mBind_mPure_comp]

@[simp] theorem mBind_mMap_left {f : α → β} (hf : Measurable f) (x : m α)
    {g : β → m γ} (hg : Measurable g) :
    ((f <$>ₘ x) >>=ₘ fun b => g b) = (x >>=ₘ fun a => g (f a)) := by
  rw [← mBind_mPure_comp hf]
  simp (disch := fun_prop) only [mBind_assoc, mPure_mBind]

end Lawful

section MeasurableSpaceFor

universe uρ uα u v

variable {α : Type u} [mα : MeasurableSpace α] (m : (α : Type u) → [MeasurableSpace α] → Type v)
  {m' : (α : Type u) → Type v}

instance instMeasurableSpace {β : Type u} [mβ : MeasurableSpace β] :
    MeasurableSpace (ForInStep β) := mβ.map ForInStep.yield ⊓ mβ.map ForInStep.done

class MeasurableSpaceForIn (ρ : Type uρ) (α : outParam (Type uα)) where
  forIn {β : Type u} [σβ : MeasurableSpace β] (x : ρ) (b : β)
    (f : α → β → m (ForInStep β)) : m β

class MeasurableSpaceForIn' (ρ : Type uρ) (α : outParam (Type uα))
    (d : outParam (Membership α ρ)) where
  forIn' {β : Type u} [σβ : MeasurableSpace β] (x : ρ) (b : β)
    (f : (a : α) → a ∈ x → β → m (ForInStep β)) : m β

instance (priority := 500) instMeasurableSpaceForInOfForIn'
    {ρ : Type uρ} {α : Type uα} {d : Membership α ρ} [MeasurableSpaceForIn' m ρ α d] :
    MeasurableSpaceForIn m ρ α where
  forIn x b f := MeasurableSpaceForIn'.forIn' x b fun a _ s => f a s

end MeasurableSpaceFor

section Instances

universe u v

def Monad.toMeasurableSpaceMonad (m : Type u → Type v) [Monad m] (α : Type u) [MeasurableSpace α] :
    Type v := m α

instance {m : Type u → Type v} [Monad m] :
    MeasurableSpaceMonad (Monad.toMeasurableSpaceMonad m) where
  mPure := pure
  mBind := bind

abbrev PseudoRandom := Monad.toMeasurableSpaceMonad Rand

open MeasureTheory

open MeasurableSpacePure MeasurableSpaceBind MeasurableSpaceFunctor MeasurableSpaceMonad

noncomputable instance : MeasurableSpaceMonad Measure where
  mPure := Measure.dirac
  mBind := Measure.bind

instance : LawfulMeasurableSpaceMonad Measure where
  mMap_const := by simp [mMapConst, mMap]
  id_mMap μ := by simp [mMap]
  mPure_measurable := by unfold mPure; fun_prop
  mBind_measurable := by unfold mBind; fun_prop
  mBind_mPure_comp _ _ := by rfl
  mPure_mBind x _ hf := Measure.dirac_bind hf x
  mBind_assoc _ _ _ hf hg := Measure.bind_bind hf.aemeasurable hg.aemeasurable

end Instances
