module

public import VerifiedGarbage.Proof.AesSiv.Words
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-SIV on RISC-V: the counter's words

Untrusted: everything here is checked by Lean. The counter `Q + i` is kept
at `W + 64` as two doublewords whose bytes are the halves of the 128-bit
integer, big-endian (`le8_rev`): the second is read and written a byte at a
time, big-endian (`loadBE64`, `storeBE`), which loads and stores the
byte-reversed doubleword (`BE64.wp_loadBE64`, `BE64.wp_storeBE8`). `counter` clears bit 7 of the
IV's bytes 8 and 12 by setting and flipping it (`orr_eor`), which leaves the
counter's second doubleword below `2⁶³` (`counter_low64`), so adding to that
doubleword alone, fewer than `2⁶³` in all, adds to the integer (`add_lo`).
As on PPC64LE (`Proof/AesSiv/PPC64LE/Counter.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG
open VG.Proof.Cmac (le8 length_le8)
open VG.Proof.AesCcm (beVal beVal_append beVal_cons beVal_lt)

/-- Storing the byte-reversed halves of `h ++ l` stores its bytes, big-endian. -/
theorem le8_rev (h l : BitVec 64) :
    le8 (byteRev64 h) ++ le8 (byteRev64 l) = Spec.Gcm.toBytes (h ++ l) := by
  refine Proof.Cmac.ext16 (by simp [length_le8]) (Proof.Cmac.toBytes_length _) fun k hk => ?_
  rw [Proof.Aes.toBytes_getD _ hk]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp only [hj, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge k 8 with h8 | h8
  · rw [getD_le8_append _ _ hk]
    simp only [h8, ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb', byteRev64_getLsbD _ (by omega)]
    simp only [hj, decide_true, Bool.true_and, show ¬ 8 * (15 - k) + j < 64 by omega, ite_false]
    congr 1; omega
  · rw [getD_le8_append _ _ hk]
    simp only [show ¬ k < 8 by omega, ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb', byteRev64_getLsbD _ (by omega)]
    simp only [hj, decide_true, Bool.true_and, show 8 * (15 - k) + j < 64 by omega, ite_true]
    congr 1; omega

theorem rev64_rev64 (a : BitVec 64) : byteRev64 (byteRev64 a) = a := Proof.Gcm.byteRev64_byteRev64 a

/-- Adding to the low doubleword, without a carry, adds to the integer. -/
theorem add_lo (hi lo : BitVec 64) {k : Nat} (h : lo.toNat + k < 2 ^ 64) :
    (hi ++ (lo + BitVec.ofNat 64 k) : BitVec 128) = (hi ++ lo : BitVec 128) + BitVec.ofNat 128 k := by
  apply BitVec.eq_of_toNat_eq
  have hl := lo.isLt
  have hh := hi.isLt
  simp only [BitVec.toNat_append, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show k < 2 ^ 128 by omega),
    Nat.mod_eq_of_lt h, ← Nat.shiftLeft_add_eq_or_of_lt h, ← Nat.shiftLeft_add_eq_or_of_lt hl,
    Nat.shiftLeft_eq]
  have : hi.toNat * 2 ^ 64 + lo.toNat + k < 2 ^ 128 := by
    have : hi.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
    omega
  rw [Nat.mod_eq_of_lt this]
  omega

/-- The bits `counter` sets and flips: bit 7 of the doubleword's bytes 0 and 4. -/
def qbits : BitVec 64 := 0x8000000080

/-- Setting the bits and flipping them clears them. -/
theorem orr_eor (x : BitVec 64) : (x ||| qbits) ^^^ qbits = x &&& qmask := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have hb : ∀ j < 64, qbits.getLsbD j = decide (j = 7 ∨ j = 39) := by decide
  have hq : ∀ j < 64, qmask.getLsbD j = !decide (j = 7 ∨ j = 39) := by decide
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and, hb j hj, hq j hj]
  cases x.getLsbD j <;> by_cases h : j = 7 ∨ j = 39 <;> simp [h]

/-- The counter `Q`'s last 64 bits, as a big-endian integer, are below `2⁶³`. -/
theorem counter_low64 (v : List Byte) : Spec.Siv.beNat (Spec.Siv.counter v) % 2 ^ 64 < 2 ^ 63 := by
  have e : Spec.Siv.counter v = ((List.range 8).map fun i => v.getD i 0) ++
      [v.getD 8 0 &&& 0x7f, v.getD 9 0, v.getD 10 0, v.getD 11 0, v.getD 12 0 &&& 0x7f, v.getD 13 0,
        v.getD 14 0, v.getD 15 0] := by
    simp [Spec.Siv.counter, List.range_succ]
  rw [e, show Spec.Siv.beNat = beVal from rfl, beVal_append]
  simp only [List.length_cons, List.length_nil]
  have hr := beVal_lt [v.getD 9 0, v.getD 10 0, v.getD 11 0, v.getD 12 0 &&& 0x7f, v.getD 13 0, v.getD 14 0,
    v.getD 15 0]
  simp only [List.length_cons, List.length_nil] at hr
  rw [beVal_cons]
  simp only [List.length_cons, List.length_nil]
  have h0 : (v.getD 8 0 &&& 0x7f).toNat < 128 := by
    rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  generalize beVal [v.getD 9 0, v.getD 10 0, v.getD 11 0, v.getD 12 0 &&& 0x7f, v.getD 13 0, v.getD 14 0,
    v.getD 15 0] = r at hr ⊢
  generalize (v.getD 8 0 &&& 0x7f).toNat = b at h0 ⊢
  simp only [Nat.reducePow, Nat.reduceAdd] at hr ⊢
  omega

end VG.Proof.AesSiv.RISCV64
