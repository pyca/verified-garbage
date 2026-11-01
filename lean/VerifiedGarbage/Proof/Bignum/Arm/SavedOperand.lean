module
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Bignum.Arm.SavedOperand
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandState

import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandArgs
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperand
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block

/-! # Exact import of private-key bytes using the saved call arguments -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem savedOperand_ok (s : State) {base src : BitVec 32} {len w k ps cs o : Nat} {bs : List Byte}
    (h : ArithmeticReady base len w s) (source : SavedOperand base src len k ps cs bs s)
    (ho : o < 8) (ho0 : o ≠ 0) (positive : 0 < k) (fit : k ≤ 8 * w) :
    WP isa (savedOperand o ps cs) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w o = Spec.Rsa.os2ip bs ∧ Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [savedOperand, WP.seq_iff]
  refine WP.mono (savedOperandArgs_ok s source) ?_
  rintro u ⟨ptrU, countU, memU, restU⟩
  have ready := h.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ptr)
  refine WP.mono (importOperand_ok u ready ho ho0 positive fit source.source.fits
    (by rw [restU.rd, restU.wr]; exact source.source.read) source.sourceSeparate ptrU countU) ?_
  rintro t ⟨done, value, keeps, frame, rest⟩
  rw [memU, source.source.bytes] at value
  rw [memU] at keeps frame
  exact ⟨done, value, keeps, frame, (restU.mono (by decide)).trans rest⟩

end VG.Proof.Bignum.Arm
