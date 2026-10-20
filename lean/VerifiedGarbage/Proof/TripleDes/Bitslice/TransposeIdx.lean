module


/-!
# The indices of the bitsliced state's transposition

The transposition of the 64 state words runs in two stages of 8 × 8 bit
blocks (`stA`, `stB` on each target): this is the index arithmetic that says
they compose to the transposition, shared by every target. It is proven from
facts about one index at a time, 64 cases each, rather than by deciding all
4096 pairs.
-/

@[expose] public section

namespace VG.Proof.TripleDes.Bitslice

theorem low_high_bits : ∀ p < 64, p &&& 7 = p % 8 ∧ p &&& 56 = 8 * (p / 8) := by decide

theorem byte_bits : ∀ c < 8, ∀ b < 8, (8 * c ||| b) = 8 * c + b ∧ ((8 * c + b) >>> 3) &&& 7 = c ∧
    (8 * c + b) &&& 7 = b ∧ (b ||| (c <<< 3)) = 8 * c + b := by decide

theorem stB_stA_idx : ∀ j < 64, ∀ p < 64,
    (8 * (j / 8) + (p &&& 7)) % 8 + 8 * ((((p &&& 56) ||| (j % 8)) >>> 3) &&& 7) = p ∧
    ((((p &&& 56) ||| (j % 8)) &&& 7) ||| (((8 * (j / 8) + (p &&& 7)) / 8) <<< 3)) = j ∧
    ((p &&& 56) ||| (j % 8)) < 64 := by
  intro j hj p hp
  obtain ⟨p1, p2⟩ := low_high_bits p hp
  obtain ⟨c1, c2, c3, -⟩ := byte_bits (p / 8) (by omega) (j % 8) (Nat.mod_lt _ (by decide))
  obtain ⟨-, -, -, c4⟩ := byte_bits (j / 8) (by omega) (j % 8) (Nat.mod_lt _ (by decide))
  rw [p1, p2, c1, c2, c3, show (8 * (j / 8) + p % 8) / 8 = j / 8 by omega, c4]
  omega

end VG.Proof.TripleDes.Bitslice
