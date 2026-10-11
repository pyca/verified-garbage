import VerifiedGarbage.Proof.Idea.KeyBits
import VerifiedGarbage.Impl.Idea.Key32

/-!
# IDEA key expansion, bit by bit, on 32-bit words

As `KeyBits.lean`, for the 32-bit targets: key bit `i` is at the bit
`keyLoc32` gives of one of the key's four little-endian 32-bit words
(`keyLoc32_spec`), and a subkey's bits are bits of a 32-bit word of the
schedule in memory (`scheduleAt_getLsbD32`).
-/

namespace VG.Proof.Idea

open VG

theorem keyLoc32_spec {i : Nat} (hi : i < 128) :
    (Impl.Idea.keyLoc32 i).1 < 4 ∧ (Impl.Idea.keyLoc32 i).2 < 32 ∧
      4 * (Impl.Idea.keyLoc32 i).1 + (Impl.Idea.keyLoc32 i).2 / 8 = 15 - i / 8 ∧
      (Impl.Idea.keyLoc32 i).2 % 8 = i % 8 := by
  simp only [Impl.Idea.keyLoc32]
  omega

/-- Bit `t` of a little-endian 32-bit word in memory. -/
theorem readW32_getLsbD (m : Mem) (a : Addr) {t : Nat} (ht : t < 32) :
    (m.readW a 32).getLsbD t = (m (a + BitVec.ofNat 64 (t / 8))).getLsbD (t % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 4) (j := t / 8) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq, show t % 8 < 8 from Nat.mod_lt _ (by decide),
    decide_true, Bool.true_and]
  congr 1; omega

/-- Bit `b` of subkey `n` is a bit of 32-bit word `n / 2` of the schedule. -/
theorem scheduleAt_getLsbD32 (m : Mem) (p : Addr) {n b : Nat} (hn : n < 52) (hb : b < 16) :
    ((Spec.Idea.scheduleAt m p).getD n 0).getLsbD b =
      (m.readW (p + BitVec.ofNat 64 (4 * (n / 2))) 32).getLsbD (16 * (n % 2) + b) := by
  rw [scheduleAt_getD m p hn, readW32_getLsbD _ _ (by omega), Offset.add_ofNat_add_ofNat,
    BitVec.getLsbD_append]
  by_cases h : b < 8
  · simp only [h, ↓reduceIte]
    rw [show 4 * (n / 2) + (16 * (n % 2) + b) / 8 = 2 * n by omega,
      show (16 * (n % 2) + b) % 8 = b by omega]
  · simp only [h, ↓reduceIte]
    rw [show 4 * (n / 2) + (16 * (n % 2) + b) / 8 = 2 * n + 1 by omega,
      show (16 * (n % 2) + b) % 8 = b - 8 by omega]

end VG.Proof.Idea
