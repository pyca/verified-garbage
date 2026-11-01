module

public import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-!
# RSA private keys on x86-64: masks, and the arrays' separation and bases

The masks of a conjunction and of a word's low bit (`mask_and'`,
`mask_low`), arrays apart (`slot_far`), and two bases at once (`base2_ok`),
which the key routines' proofs share. The inverse itself is
`InvB/Main.lean`'s `inverse_ok`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem mask_and' (a b : Bool) : mask a &&& mask b = mask (a && b) := by
  cases a <;> cases b <;> rfl

/-- The mask of a word's low bit. -/
theorem mask_low (x : BitVec 64) : BitVec.setWidth 64 (0 : BitVec 32) - (x &&& 1) =
    mask (decide (x.toNat % 2 = 1)) := by
  have h2 : x &&& 1 = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega_using []
  rw [h2]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- Three distinct arrays among sixteen are apart. -/
theorem slot_far {w i j : Nat} (h : i ≠ j) : slot w i + 8 * (w + 2) ≤ slot w j ∨ slot w j + 8 * (w + 2) ≤ slot w i :=
  slot_sep h

/-- Two bases. -/
theorem base2_ok {s : State} {B : Addr} {w : Nat} (i j : Nat) {r₁ r₂ : Reg} (h₁ : r₁ ≠ .r9) (h₂ : r₂ ≠ .r9)
    (h₁₂ : r₂ ≠ r₁) (hdi : s.gpr .rdi = B) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) (hr1 : r₁ ≠ .rdi) :
    WP isa (.block (base i r₁ ++ base j r₂)) s fun t =>
      t.gpr r₁ = off B (slot w i) ∧ t.gpr r₂ = off B (slot w j) ∧ t.mem = s.mem ∧ Keep [r₁, r₂] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (base_ok i h₁ hdi h9) fun t₁ ⟨e₁, m₁, k₁⟩ => ?_
  have g1 : ∀ r, r ≠ r₁ → t₁.gpr r = s.gpr r := fun r h => k₁.gpr (by simp [h])
  refine WP.mono (base_ok j h₂ ((g1 _ (Ne.symm hr1)).trans hdi) ((g1 _ (Ne.symm h₁)).trans h9))
    fun t ⟨e₂, m₂, k₂⟩ => ?_
  have g2 : ∀ r, r ≠ r₂ → t.gpr r = t₁.gpr r := fun r h => k₂.gpr (by simp [h])
  exact ⟨(g2 _ (Ne.symm h₁₂)).trans e₁, e₂, m₂.trans m₁, (k₁.trans k₂).mono (by simp)⟩

end VG.Proof.Rsa.X86_64
