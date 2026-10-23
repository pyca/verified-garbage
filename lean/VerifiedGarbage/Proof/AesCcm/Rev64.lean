module

public import VerifiedGarbage.Proof.Framework.Bswap

/-!
# AES-CCM: byte reversal of shifted and combined words

Untrusted: everything here is checked by Lean, and nothing depends on a
target. A target that stores a word byte-reversed (PPC64LE's `stdbrx`)
builds the blocks AArch64 builds by reversing a word in a register (`rev`)
and storing it little-endian, with its shifts on the other side:
`byteRev64` distributes over OR (`byteRev64_or`) and turns a left shift by
whole bytes into a right shift (`byteRev64_shl`).
-/

@[expose] public section

namespace VG.Proof.AesCcm

open VG

theorem byteRev64_or (a b : BitVec 64) : byteRev64 (a ||| b) = byteRev64 a ||| byteRev64 b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, byteRev64_getLsbD _ hi, byteRev64_getLsbD _ hi, byteRev64_getLsbD _ hi,
    BitVec.getLsbD_or]

theorem byteRev64_shl (a : BitVec 64) {k : Nat} (hk : k ≤ 8) :
    byteRev64 (a <<< (8 * k)) = byteRev64 a >>> (8 * k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [byteRev64_getLsbD _ hi, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, Nat.add_comm (8 * k) i]
  by_cases h : i + 8 * k < 64
  · rw [byteRev64_getLsbD _ h]
    have e₁ : ¬ 8 * (7 - i / 8) + i % 8 < 8 * k := by
      have : i / 8 + k ≤ 7 := by omega
      omega
    have e₂ : 8 * (7 - i / 8) + i % 8 - 8 * k = 8 * (7 - (i + 8 * k) / 8) + (i + 8 * k) % 8 := by omega
    simp only [e₁, decide_false, Bool.not_false, Bool.true_and, e₂, show 8 * (7 - i / 8) + i % 8 < 64 by omega,
      decide_true]
  · have e₁ : 8 * (7 - i / 8) + i % 8 < 8 * k := by omega
    simp only [e₁, decide_true, Bool.not_true, Bool.and_false, Bool.false_and]
    exact (BitVec.getLsbD_of_ge (byteRev64 a) (i + 8 * k) (by omega)).symm

end VG.Proof.AesCcm
