module

public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Blocks in and out of a register, a byte at a time

`loadBE64` reads the block's bytes big-endian (`be64`), its `decodeBlock`;
`storeBE 8` writes a word's bytes big-endian (`beBytes 8`), its
`encodeBlock`. The halves of a word are split and joined with shifts.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64.ByteLoad VG.WriteBytes VG.Spec.TripleDes

theorem be64_decode (m : Mem) (p : Addr) (off : Nat) :
    be64 m p off = decodeBlock (blockAt m (p + BitVec.ofNat 64 off)) := by
  rw [VG.Proof.TripleDes.decodeBlock_cat]
  simp only [be64, VG.Proof.TripleDes.catBlock, blockAt, Vector.getElem_ofFn,
    Offset.add_ofNat_add_ofNat]
  rfl

theorem stored_block (m : Mem) (q : Addr) (x : BitVec 64) :
    blockAt (writeBytes m q (beBytes 8 x)) q = encodeBlock x := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, encodeBlock, Vector.getElem_ofFn, writeBytes, Offset.add_sub_cancel_left,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), List.getD_eq_getElem?_getD,
    beBytes, List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some,
    List.length_map, List.length_range, hi, ite_true, Nat.reduceSub]

theorem stored_frame (m : Mem) (q : Addr) (x : BitVec 64) :
    Frame [⟨q, 8⟩] m (writeBytes m q (beBytes 8 x)) :=
  writeBytes_frame _ _ _ (by rw [beBytes_length]; exact Region.contains_self q 8)

theorem upperHalf_extend (x : BitVec 64) :
    x >>> 32 = ((x >>> 32).setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h : j < 32
  · simp only [h, hj, decide_true, Bool.true_and]
  · have hz : x.getLsbD (32 + j) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp only [h, hj, decide_false, decide_true, Bool.false_and, Bool.true_and, hz]

theorem lowerHalf_extend (x : BitVec 64) :
    x <<< 32 >>> 32 = (x.setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases h : j < 32
  · simp (disch := omega) only [h, hj, decide_true, Bool.true_and, show 32 + j < 64 by omega,
      show ¬ 32 + j < 32 by omega, decide_false, Bool.not_false, show 32 + j - 32 = j by omega]
  · simp only [h, decide_false, Bool.false_and, show ¬ 32 + j < 64 by omega, Bool.and_false]

theorem join_halves (x : BitVec 64) :
    (((x >>> 32).setWidth 32).setWidth 64 <<< 32) ^^^ (x.setWidth 32).setWidth 64 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hj, decide_true, Bool.true_and]
  by_cases h : j < 32
  · simp [h]
  · simp (disch := omega) [h, show j - 32 < 32 by omega, show 32 + (j - 32) = j by omega,
      show j - 32 < 64 by omega]

end VG.Proof.TripleDes.RISCV64
