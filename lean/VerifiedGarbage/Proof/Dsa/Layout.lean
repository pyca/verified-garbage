module

public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Bounds of the DSA scratch layout -/

@[expose] public section

namespace VG.Proof.Dsa

open VG.Impl.Dsa.Layout VG.Proof.Bignum

/-- The packed widths fit the two Montgomery workspaces, including the
224-bit subgroup's partial high limb. -/
theorem workspace_bounds {pLen qLen : Nat} (h : Spec.Dsa.lengthsValid pLen qLen) :
    2 ≤ (pLen + 7) / 8 ∧ (pLen + 7) / 8 ≤ outerWords ∧
    2 ≤ (qLen + 7) / 8 ∧ (qLen + 7) / 8 ≤ outerWords ∧
    slot outerWords 8 ≤ pWorkspace ∧
    pWorkspace + slot ((pLen + 7) / 8) 8 + tabBytes ((pLen + 7) / 8) ≤ qWorkspace ∧
    qWorkspace + slot ((qLen + 7) / 8) 8 + tabBytes ((qLen + 7) / 8) ≤ activeBytes ∧
    usedBytes ≤ 8 * Spec.Dsa.scratchWords pLen := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- All local operands are outside the arithmetic prefix and mutually
separate at their maximum lengths. -/
theorem scalar_buffer_bounds :
    activeBytes ≤ r ∧ r + 32 ≤ s ∧ s + 32 ≤ inverse ∧ inverse + 32 ≤ u ∧
    u + 32 ≤ v ∧ v + 32 ≤ z ∧ z + 32 ≤ qMinusTwo ∧ qMinusTwo + 32 ≤ t ∧
    t + 384 ≤ t2 ∧ t2 + 384 ≤ usedBytes := by decide

/-- Saved arguments lie after the parent header and before either child. -/
theorem field_bounds (f : Field) :
    256 ≤ f.offset ∧ f.offset + 8 ≤ pWorkspace := by cases f <;> decide

end VG.Proof.Dsa
