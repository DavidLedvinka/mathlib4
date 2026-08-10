import Mathlib.Tactic.Inclusion.Experimental.Tests

open Lean Meta

namespace Inclusion.NativeTests

open Inclusion.Tests

example : True := by
  inclusion +native

example : True := by
  inclusion (native := true)

example : parameterizedTrue := by
  inclusion +native [testParam := 7]

example {x : ℝ} (hx : x ∈ Inclusion.Tests.unitInterval) : x + x ≤ 4 := by
  inclusion +native

def nativeOnlyProp : Prop := True

unsafe def nativeOnlyCheckImpl : IntervalBool := .true

@[implemented_by nativeOnlyCheckImpl]
def nativeOnlyCheck : IntervalBool := .undetermined

theorem nativeOnlyProp_mem : nativeOnlyProp ∈ nativeOnlyCheck := by
  exact mem_intervalBool_undetermined _

@[inclusionExt nativeOnlyProp]
meta def evalNativeOnlyProp : InclusionExt where
  family := `core
  derive e := do
    unless e.isConstOf ``nativeOnlyProp do failure
    return ⟨mkConst ``nativeOnlyCheck, mkConst ``nativeOnlyProp_mem⟩

example : nativeOnlyProp := by
  inclusion +native

example : True := by
  fail_if_success
    have : nativeOnlyProp := by
      inclusion +kernel
  trivial

def kernelOnlyProp : Prop := True

unsafe def kernelOnlyCheckImpl : IntervalBool := .undetermined

@[implemented_by kernelOnlyCheckImpl]
def kernelOnlyCheck : IntervalBool := .true

theorem kernelOnlyProp_mem : kernelOnlyProp ∈ kernelOnlyCheck := by
  exact mem_intervalBool_true trivial

@[inclusionExt kernelOnlyProp]
meta def evalKernelOnlyProp : InclusionExt where
  family := `core
  derive e := do
    unless e.isConstOf ``kernelOnlyProp do failure
    return ⟨mkConst ``kernelOnlyCheck, mkConst ``kernelOnlyProp_mem⟩

example : kernelOnlyProp := by
  inclusion +kernel

example : True := by
  fail_if_success
    have : kernelOnlyProp := by
      inclusion +native
  trivial

end Inclusion.NativeTests
