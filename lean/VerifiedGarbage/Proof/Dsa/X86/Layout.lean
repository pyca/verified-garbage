module

public import VerifiedGarbage.Impl.Dsa.X86.Layout
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Impl.Mont.X86.Context
import VerifiedGarbage.Proof.Framework.Omega

/-! # Bounds for the reused arithmetic context and persistent DSA values -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Layout
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86.Layout VG.Impl.Mont.X86.Dynamic

theorem context_bound {n : Nat} (hn : n ≤ 48) : contextBytes n ≤ 7048 := by
  simp only [contextBytes, slot, stride]
  omega

theorem field_bounds (f : Field) : 8192 ≤ field f ∧ field f + 4 ≤ saved := by
  cases f <;> decide

theorem scalar_bounds {a : Nat} (ha : a ∈ scalars) :
    8272 ≤ a ∧ a + 32 ≤ t := by
  simp only [scalars, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem wide_bounds {a : Nat} (ha : a ∈ wideValues) :
    8272 ≤ a ∧ a + 384 ≤ usedBytes := by
  simp only [wideValues, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;> decide

theorem scratch_bound {pLen qLen : Nat} (h : VG.Spec.Dsa.lengthsValid pLen qLen) :
    usedBytes ≤ 8 * VG.Spec.Dsa.scratchWords pLen := by
  unfold VG.Spec.Dsa.lengthsValid at h
  unfold VG.Spec.Dsa.scratchWords usedBytes
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

end VG.Proof.Dsa.X86.Layout
