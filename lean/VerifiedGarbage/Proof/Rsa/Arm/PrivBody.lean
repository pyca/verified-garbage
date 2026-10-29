module
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext

import VerifiedGarbage.Proof.Rsa.Arm.PrivCheck
import VerifiedGarbage.Proof.Rsa.Arm.PrivCheckFrame
import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtCall

/-! # The complete private-operation body satisfies the shared RSA outcome -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem privateBody_ok (v : CrtImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} (s : State)
    (h : PrivContext g bs s) (output : s.gpr .r0 = g.output)
    (modulus : s.gpr .r2 = g.sources 0) (count : s.gpr .r3 = BitVec.ofNat 32 g.length) :
    WP isa (body v.name v.code v.pcName v.pc v.pdName v.pd) s fun t =>
      Spec.Rsa.writtenOutcome t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateChecked (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7)) ∧
      Spec.Rsa.bytesAt t.mem (State.addr g.temporary) g.length = List.replicate g.length 0 ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r4, .r12, .lr] s t := by
  unfold body
  refine WP.seq (WP.mono (crtArgs_ok s h output modulus count) ?_)
  rintro u ⟨hu, slotsU, argsU, frameU, restU⟩
  refine WP.seq (WP.mono (crt_call v hu slotsU argsU) ?_)
  rintro z ⟨hz, slotsZ, frameZ, restZ, crt⟩
  refine WP.mono (check_ok v z hz slotsZ) ?_
  rintro t ⟨_, status, bytes, cleared, frameT, restT⟩
  refine ⟨?_, cleared, (frameU.mono (by simp [bodyWrites])).trans
    ((frameZ.sub (calleeWrites_sub (crtWrites_sub h.valid))).trans frameT),
    (restU.mono (by simp)).trans ((restZ.mono (by simp [callClobbers])).trans restT)⟩
  have narrow : ((z.gpr .r0).setWidth 64).setWidth 32 = z.gpr .r0 := by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have outcome := Rsa.outcome_eq (rc := (z.gpr .r0).setWidth 64)
    (r := Rsa.checkResult ((z.gpr .r0).setWidth 64) (bs 0) (bs 1) (bs 2)
      (Spec.Rsa.bytesAt z.mem (State.addr g.temporary) g.length))
    (h.sources 0).length (h.sources 2).length (by rw [narrow]; exact crt) rfl bytes
  rw [status]
  exact outcome
end VG.Proof.Rsa.Arm
