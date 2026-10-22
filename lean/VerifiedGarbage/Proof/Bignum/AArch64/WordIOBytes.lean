module
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Spec.Rsa

import VerifiedGarbage.Proof.Bignum.ByteDigits
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# Big-endian words on AArch64: `rev`

`rev` maps byte `j` of a word to byte `7 - j` (`rev64_byte`), so `rev` of the
eight bytes at `src + k - 8 (q + 1)`, read little-endian, is digit `q` (in
radix `2^64`) of the OS2IP of the `k` bytes at `src` (`read_digit`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WordIO

open VG VG.AArch64 VG.Proof.Bignum.ByteDigits

/-- Byte reversal maps byte `j` to byte `7 - j`. -/
theorem rev64_byte (v : BitVec 64) {j : Nat} (hj : j < 8) :
    (rev64 v).extractLsb' (8 * j) 8 = v.extractLsb' (8 * (7 - j)) 8 := by
  ext r hr
  simp only [BitVec.getElem_extractLsb', rev64, VG.AArch64.getLsbD_append_block _ _ _ hr]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    h | h | h | h | h | h | h | h <;> subst h <;>
  simp (disch := omega) only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add,
    Nat.reduceMul, BitVec.getLsbD_extractLsb', decide_eq_true, Bool.true_and, Nat.add_comm]

theorem read_digit {m : Mem} {src : Addr} {bs : List Byte} {q : Nat} (hq : 8 * (q + 1) ≤ bs.length)
    (hb : ∀ i (hi : i < bs.length), m (src + BitVec.ofNat 64 i) = bs[i]) :
    rev64 (m.read (src + BitVec.ofNat 64 (bs.length - 8 * (q + 1))) 8) =
      BitVec.ofNat 64 (Spec.Rsa.os2ip bs / 256 ^ (8 * q)) := by
  apply eq_of_bytes
  intro j hj
  rw [rev64_byte _ hj, extract_nat _ hj, Mem.extractLsb'_read _ _ (by omega), BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, hb _ (by omega), os2ip_byte]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  omega

end VG.Proof.Bignum.AArch64.WordIO
