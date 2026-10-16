module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicResult
public import VerifiedGarbage.Proof.Bignum.Arm.ExportMasked
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Public RSA output serialization and branchless rejection -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem publicFinish_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicResult base dst np ep xp len k eLen nb eb xb s) :
    WP isa PublicFn.finish s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb then
          Spec.Rsa.i2osp (Spec.Rsa.powMod (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip nb)) k
         else List.replicate k 0) ∧
      t.gpr .r0 = BitVec.ofNat 32 (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)).toNat ∧
      Frame [⟨State.addr dst, k⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [PublicFn.finish, WP.seq_iff]
  refine WP.mono (publicOutputArgs_ok s h.stack) ?_
  rintro u ⟨index, output, count, memU, restU⟩
  have ready := h.ready.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.ready.ptr)
  have dims := pc_dimensions h.buffers.minLength h.buffers.maxLength h.buffers.space
  refine WP.mono (exportMasked_ok u ready.workspace ready.layout ready.width (by decide : 6 < 8)
    (by have := h.buffers.minLength; omega) dims.2.2.2.1 (by rw [memU]; exact h.valueFit)
    h.buffers.outputFit (by rw [restU.wr]; exact h.buffers.write) h.buffers.outputSeparate
    ready.ptr index output count (by rw [restU.sp]; have := h.stack.nowrap; omega)
    (by rw [restU.rd, restU.wr, restU.sp]; exact h.stack.read (by decide) (by decide))
    (by rw [restU.sp]; exact (h.buffers.stackOutput.sub_right (Offset.sub_base _ (by decide))).symm)
    (by rw [memU, restU.sp]; exact h.flag)) ?_
  rintro t ⟨bytes, status, frame, restT⟩
  rw [memU, h.value] at bytes
  rw [memU] at frame
  exact ⟨by simpa only [decide_eq_true_eq] using bytes, status, frame,
    (restU.mono (by simp [roundClobbers])).trans restT⟩

end VG.Proof.Bignum.Arm
