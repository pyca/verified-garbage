import VerifiedGarbage.Proof.Camellia.X86_64.Keys

/-!
# Halves as little-endian words

The key schedule keeps the 64-bit halves of `KL`, `KR`, `KA` and `KB` as ECB
loads them: little-endian words of their big-endian bytes (`WordOf`,
`Proof/Camellia/Common.lean`). `bswap` turns such a word into the half as a
number (`bswap_of_wordOf`).
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64

theorem bswap64_bit (a : BitVec 64) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (bswap64 a).getLsbD (56 - 8 * i + j) = a.getLsbD (8 * i + j) := by
  unfold bswap64
  change BitVec.getLsbD (w := 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8) _ _ = _
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

/-- `bswap` of such a word is the half. -/
theorem bswap_of_wordOf {w h : BitVec 64} (hw : WordOf w h) : bswap64 w = h := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have h1 := bswap64_bit w (i := (63 - t) / 8) (j := t % 8) (by omega) (by omega)
  rw [show 56 - 8 * ((63 - t) / 8) + t % 8 = t by omega] at h1
  rw [h1, hw _ (by omega) _ (by omega), Camellia.getLsbD_byteOf _ (by omega) (by omega)]
  congr 1; omega

end VG.Proof.Camellia.X86_64
