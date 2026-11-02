module

public import VerifiedGarbage.Proof.Bignum.Arm.PdResult
public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
import VerifiedGarbage.Proof.Bignum.Arm.ExportMasked
import VerifiedGarbage.Proof.Bignum.Arm.PublicArgs
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # Public RSA output serialization and branchless rejection -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem pdFinish_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdResult base dst np ep xp len k eLen N R eb xb s) :
    WP isa PublicFn.finish s fun t =>
      (pdGood k N R → N < 2 ^ (8 * k) → Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if Spec.Rsa.os2ip xb < N then
          Spec.Rsa.i2osp (Spec.Rsa.powMod (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) (N)) k
         else List.replicate k 0)) ∧
      t.gpr .r0 = BitVec.ofNat 32 (decide (Spec.Rsa.os2ip xb < N)).toNat ∧
      Frame [⟨State.addr dst, k⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [PublicFn.finish, WP.seq_iff]
  refine WP.mono (publicOutputArgs_ok s h.stack) ?_
  rintro u ⟨index, output, count, memU, restU⟩
  have ready := h.ready.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ready.ptr)
  have dims := pc_dimensions h.buffers.minLength h.buffers.maxLength h.buffers.space
  refine WP.mono (exportMasked_truncated_ok u ready.workspace ready.layout ready.width (by decide : 6 < 8)
    (by have := h.buffers.minLength; omega) dims.2.2.2.1
    h.buffers.outputFit (by rw [restU.wr]; exact h.buffers.write) h.buffers.outputSeparate
    ready.ptr index output count (by rw [restU.sp]; have := h.stack.nowrap; omega)
    (by rw [restU.rd, restU.wr, restU.sp]; exact h.stack.read (by decide) (by decide))
    (by rw [restU.sp]; exact (h.buffers.stackOutput.sub_right (Offset.sub_base _ (by decide))).symm)
    (by rw [memU, restU.sp]; exact h.flag)) ?_
  rintro t ⟨bytes, status, frame, restT⟩
  rw [memU] at bytes
  rw [memU] at frame
  refine ⟨?_, status, frame,
    (restU.mono (by decide)).trans restT⟩

  intro good bound
  have valueFit : Proof.Rsa.Mont.numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 6 < 2 ^ (8 * k) := by
    rw [h.value good, VG.Proof.Bignum.powMod_eq]
    exact Nat.lt_trans (Nat.mod_lt _ h.positive) bound
  rw [Nat.mod_eq_of_lt valueFit, h.value good] at bytes
  simpa only [decide_eq_true_eq] using bytes

end VG.Proof.Bignum.Arm
