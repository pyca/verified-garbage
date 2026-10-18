module

public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega

/-! # The public operation from precomputed values: what an exponentiation changes, and the modulus' size -/

@[expose] public section

namespace VG.Proof.Bignum

open VG VG.Impl.Bignum VG.Impl.Bignum.Public

/-- What an exponentiation from precomputed values changes: `pdAll` but for the
input, `-m⁻¹` and the mask. -/
def expAll (w : Nat) : List (Nat × Nat) :=
  [(slot w aOne, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] ++ pExpRanges w

theorem expAll_sub (w : Nat) : ∀ r ∈ expAll w, r ∈ pdAll w := by
  intro r hr
  simp only [expAll, pdAll, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with (h | h) | h
  · exact .inl (.inr (.inr (.inr (.inl h))))
  · exact .inl (.inr (.inr (.inr (.inr h))))
  · exact .inr h

/-- The checks bound the modulus below: its top word is not zero. -/
theorem checks_big {m : Mem} {B : Addr} {w : Nat} (hw : 2 ≤ w)
    (h : (decide ((word m B (slot w aN)).toNat % 2 = 1) &&
      decide (wv m B (slot w aR2) w < wv m B (slot w aN) w) &&
      decide (word m B (slot w aN + 8 * (w - 1)) ≠ 0)) = true) :
    2 ^ (64 * (w - 1)) ≤ wv m B (slot w aN) w := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h3⟩ := h
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega_using [hw]⟩
  rw [Nat.add_sub_cancel] at h3 ⊢
  have ht : (word m B (slot (v + 1) aN + 8 * v)).toNat ≠ 0 := fun h0 => h3 (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  rw [wv]
  have : 2 ^ (64 * v) ≤ 2 ^ (64 * v) * (word m B (slot (v + 1) aN + 8 * v)).toNat :=
    Nat.le_mul_of_pos_right _ (by omega_using [ht])
  omega_using [this]

end VG.Proof.Bignum
