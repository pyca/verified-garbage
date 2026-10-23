module

public import VerifiedGarbage.Proof.Cmac.Mem32
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Proof.AesGcm.Bytes
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM: `J₀` and its increment from words

Untrusted: everything here is checked by Lean, and nothing depends on a
target. A block is the big-endian words of its four little-endian words
(`ofBytes_le4`), and `inc₃₂` increments the last of them (`inc32_words`), as
an implementation reading the last word byte-reversed adds one to it. A
word write is a write of its four bytes (`writeW32_eq`). As in
`Proof/AesGcm/Arm/J0.lean`.
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG VG.WriteBytes
open VG.Spec.Gcm (inc32 ofBytes)
open VG.Proof.Cmac (le4)

theorem inc32_words (a b c d : BitVec 32) : inc32 (a ++ b ++ c ++ d) = a ++ b ++ c ++ (d + 1) := by
  have h₁ : (a ++ b ++ c ++ d).extractLsb' 32 96 = a ++ b ++ c := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    simp only [show ¬ (32 + i < 32) by omega, ite_false, show 32 + i - 32 = i by omega]
  have h₂ : (a ++ b ++ c ++ d).extractLsb' 0 32 = d := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp [hi]
  simp only [inc32, h₁, h₂]

theorem le4_one : le4 (BitVec.ofNat 32 0x01000000) = [0, 0, 0, 1] := by decide

/-- A block from the bytes of its four little-endian words. -/
theorem ofBytes_le4 (a b c d : BitVec 32) :
    ofBytes (le4 a ++ le4 b ++ le4 c ++ le4 d) = byteRev32 a ++ byteRev32 b ++ byteRev32 c ++ byteRev32 d := by
  have h := Cmac.le4_rev4 (byteRev32 a) (byteRev32 b) (byteRev32 c) (byteRev32 d)
  rw [Cmac.byteRev32_byteRev32, Cmac.byteRev32_byteRev32, Cmac.byteRev32_byteRev32,
    Cmac.byteRev32_byteRev32] at h
  rw [h, Cmac.ofBytes_toBytes]

/-- A word write is a write of its bytes, least significant first. -/
theorem writeW32_eq (m : Mem) (a : Addr) (v : BitVec 32) : m.writeW a v = writeBytes m a (le4 v) := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, Proof.Cmac.length_le4]
  split
  · rename_i h
    rw [Proof.Cmac.getD_le4 _ h]
    simp
  · rfl

/-- The first counter block written a word at a time from `J₀` at `St`: its
first eight bytes, then its next four, then its last word incremented. -/
theorem initMem_eq (M : Mem) (St : Addr) :
    (((M.writeW (St + BitVec.ofNat 64 48) (M.readW St 64)).writeW (St + BitVec.ofNat 64 56)
      ((((M.writeW (St + BitVec.ofNat 64 48) (M.readW St 64)).readW (St + BitVec.ofNat 64 8) 32).setWidth
        64).setWidth 32)).writeW (St + BitVec.ofNat 64 60)
      (byteRev32 (byteRev32 ((((M.writeW (St + BitVec.ofNat 64 48) (M.readW St 64)).writeW
        (St + BitVec.ofNat 64 56) ((((M.writeW (St + BitVec.ofNat 64 48) (M.readW St 64)).readW
          (St + BitVec.ofNat 64 8) 32).setWidth 64).setWidth 32)).readW (St + BitVec.ofNat 64 12) 32)) + 1))) =
      writeBytes M (St + BitVec.ofNat 64 48)
        (Spec.Aes.bytesAt M St 12 ++ le4 (byteRev32 (byteRev32 (M.readW (St + BitVec.ofNat 64 12) 32) + 1))) := by
  have r8 : (M.writeW (St + BitVec.ofNat 64 48) (M.readW St 64)).readW (St + BitVec.ofNat 64 8) 32 =
      M.readW (St + BitVec.ofNat 64 8) 32 :=
    Mem.readW_writeW_sep ((Offset.disjoint St (d := 48) (n := 8) (e := 8) (k := 4) (by omega) (by omega)
      (by omega)).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by omega)
  rw [r8, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have r12 : ((M.writeW (St + BitVec.ofNat 64 48) (M.readW St 64)).writeW (St + BitVec.ofNat 64 56)
      (M.readW (St + BitVec.ofNat 64 8) 32)).readW (St + BitVec.ofNat 64 12) 32 =
      M.readW (St + BitVec.ofNat 64 12) 32 := by
    rw [Mem.readW_writeW_sep ((Offset.disjoint St (d := 56) (n := 4) (e := 12) (k := 4) (by omega) (by omega)
      (by omega)).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by omega)]
    exact Mem.readW_writeW_sep ((Offset.disjoint St (d := 48) (n := 8) (e := 12) (k := 4) (by omega) (by omega)
      (by omega)).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by omega)
  rw [r12, writeW64_eq, Cmac.le8_readW, writeW32_eq _ (St + BitVec.ofNat 64 56), Cmac.le4_readW, writeW32_eq,
    show St + BitVec.ofNat 64 56 = St + BitVec.ofNat 64 48 + BitVec.ofNat 64 (Spec.Aes.bytesAt M St 8).length by
      rw [length_bytesAt, Offset.add_add],
    writeBytes_append _ _ _ _ (by rw [length_bytesAt, length_bytesAt]; omega),
    show St + BitVec.ofNat 64 60 = St + BitVec.ofNat 64 48 +
      BitVec.ofNat 64 (Spec.Aes.bytesAt M St 8 ++ Spec.Aes.bytesAt M (St + BitVec.ofNat 64 8) 4).length by
      rw [List.length_append, length_bytesAt, length_bytesAt, Offset.add_add],
    writeBytes_append _ _ _ _ (by rw [List.length_append, length_bytesAt, length_bytesAt, Cmac.length_le4]; omega),
    ← bytesAt_add]

/-- `J₀` of a 12-byte nonce at `N` written a word at a time: its first eight
bytes, its last four and the word `0x00000001`, big-endian. -/
theorem j012Mem_eq (M : Mem) (N St : Addr) :
    ((M.writeW St (M.readW N 64)).writeW (St + BitVec.ofNat 64 8) (M.readW (N + BitVec.ofNat 64 8) 32)).writeW
      (St + BitVec.ofNat 64 12) (BitVec.ofNat 32 0x01000000) =
      writeBytes M St (Spec.Aes.bytesAt M N 12 ++ [0, 0, 0, 1]) := by
  rw [writeW64_eq, Cmac.le8_readW, writeW32_eq _ (St + BitVec.ofNat 64 8), Cmac.le4_readW, writeW32_eq, le4_one,
    show St + BitVec.ofNat 64 8 = St + BitVec.ofNat 64 (Spec.Aes.bytesAt M N 8).length by rw [length_bytesAt],
    writeBytes_append _ _ _ _ (by rw [length_bytesAt, length_bytesAt]; omega),
    show St + BitVec.ofNat 64 12 = St +
      BitVec.ofNat 64 (Spec.Aes.bytesAt M N 8 ++ Spec.Aes.bytesAt M (N + BitVec.ofNat 64 8) 4).length by
      rw [List.length_append, length_bytesAt, length_bytesAt],
    writeBytes_append _ _ _ _ (by rw [List.length_append, length_bytesAt, length_bytesAt]; decide),
    ← bytesAt_add]

end VG.Proof.AesGcm
