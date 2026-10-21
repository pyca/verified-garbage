module

import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.TCB.X86.Sse

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86

/-- One low quadword, with the unused quadword zero. -/
def packed (v : BitVec 64) : BitVec 128 := (0 : BitVec 64) ++ v

@[simp] theorem qword_packed_zero (v : BitVec 64) : qword (packed v) 0 = v := by
  simp only [qword, packed, Nat.mul_zero, BitVec.extractLsb'_append_eq_right]

@[simp] theorem qword_packed_one (v : BitVec 64) : qword (packed v) 1 = 0 := by
  simp only [qword, packed, Nat.mul_one, BitVec.extractLsb'_append_eq_left]

theorem packed_add (a b : BitVec 64) : XBinOp.eval .paddq (packed a) (packed b) = packed (a+b) := by
  simp only [XBinOp.eval, qword_packed_zero, qword_packed_one]; rfl

theorem packed_shl (a : BitVec 64) {n : BitVec 8} (hn : n.toNat < 64) :
    XShiftOp.eval .psllq (packed a) n = packed (a <<< n.toNat) := by
  change (if 63 < n.toNat then 0 else
    (qword (packed a) 1 <<< n.toNat) ++ (qword (packed a) 0 <<< n.toNat)) = _
  rw [ite_eq_right (by omega), qword_packed_zero, qword_packed_one]
  change ((0#64 <<< n.toNat) ++ (a <<< n.toNat) : BitVec 128) = packed (a <<< n.toNat)
  rw [BitVec.zero_shiftLeft]
  rfl

theorem packed_shr (a : BitVec 64) {n : BitVec 8} (hn : n.toNat < 64) :
    XShiftOp.eval .psrlq (packed a) n = packed (a >>> n.toNat) := by
  change (if 63 < n.toNat then 0 else
    (qword (packed a) 1 >>> n.toNat) ++ (qword (packed a) 0 >>> n.toNat)) = _
  rw [ite_eq_right (by omega), qword_packed_zero, qword_packed_one]
  change ((0#64 >>> n.toNat) ++ (a >>> n.toNat) : BitVec 128) = packed (a >>> n.toNat)
  rw [BitVec.zero_ushiftRight]
  rfl

theorem packed_and (a b : BitVec 64) : XBinOp.eval .pand (packed a) (packed b) = packed (a &&& b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [XBinOp.eval, packed, BitVec.getLsbD_and, BitVec.getLsbD_append]
  split <;> simp_all

theorem packed_of32 (a : BitVec 32) : a.setWidth 128 = packed (a.setWidth 64) := by
  change a.setWidth 128 = packed (a.setWidth 64)
  rw [show a.setWidth 128 = (a.setWidth 64).setWidth 128 by simp]
  exact BitVec.setWidth_eq_append (by decide)

end VG.Proof.Mont.X86.Square
