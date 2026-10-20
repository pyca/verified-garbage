module
public import VerifiedGarbage.Proof.Dsa.AArch64.Execution

import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Relating independently initialized workspaces without assuming scratch equality -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem ChildReady.inverse_unique {m₁ m₂ : Mem} {B : Addr} {o w n : Nat} {i₁ i₂ : BitVec 64}
    (h₁ : ChildReady m₁ B o w n i₁) (h₂ : ChildReady m₂ B o w n i₂)
    (hw : 1 ≤ w) (ho : n % 2 = 1) : i₁ = i₂ := by
  have e₁ : (word m₁ (off B o) (slot w aN)).toNat = n % 2 ^ 64 := by
    rw [← wv_mod64 _ _ _ hw, h₁.modulus]
  have e₂ : (word m₂ (off B o) (slot w aN)).toNat = n % 2 ^ 64 := by
    rw [← wv_mod64 _ _ _ hw, h₂.modulus]
  have i₁ := h₁.inverse
  have i₂ := h₂.inverse
  rw [e₁] at i₁
  rw [e₂] at i₂
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact ho) i₁ i₂

def ExecutionLayout.withInverses (L : ExecutionLayout) (pi qi : BitVec 64) : ExecutionLayout :=
  { L with pInverse := pi, qInverse := qi }

theorem readyInverses_eq {L : ExecutionLayout} {s₁ s₂ : State} {pi₁ qi₁ pi₂ qi₂ : BitVec 64}
    (h₁ : Ready (L.withInverses pi₁ qi₁) s₁) (h₂ : Ready (L.withInverses pi₂ qi₂) s₂)
    (hp : L.modulus % 2 = 1) (hq : L.subgroup % 2 = 1) : pi₁ = pi₂ ∧ qi₁ = qi₂ := by
  obtain ⟨hp2, _, hq2, _⟩ := VG.Proof.Dsa.workspace_bounds L.lengths
  exact ⟨h₁.pChild.inverse_unique h₂.pChild (by change 1 ≤ (L.pLen + 7) / 8; omega) hp,
    h₁.qChild.inverse_unique h₂.qChild (by change 1 ≤ (L.qLen + 7) / 8; omega) hq⟩

end VG.Proof.Dsa.AArch64
