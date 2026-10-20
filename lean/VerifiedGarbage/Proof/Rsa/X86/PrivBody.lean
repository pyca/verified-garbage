module
public import VerifiedGarbage.Proof.Rsa.X86.PrivContext

import VerifiedGarbage.Proof.Rsa.X86.PrivCheck
import VerifiedGarbage.Proof.Rsa.X86.PrivRetained
import VerifiedGarbage.Proof.Rsa.X86.PrivCrtCall
import VerifiedGarbage.Proof.Framework.Contract

/-! # The complete private-operation body satisfies the shared RSA outcome -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem privateBody_ok (v : CrtImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} (s : State)
    (h : PrivContext g bs s) :
    WP isa (body v.name v.code v.pcName v.pc v.pdName v.pd) s fun t =>
      Spec.Rsa.writtenOutcome t.mem (byteAddr g.output) g.length (t.gpr .eax)
        (Spec.Rsa.privateChecked (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7)) ∧
      Spec.Rsa.bytesAt t.mem (byteAddr g.temporary) g.length = List.replicate g.length 0 ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  unfold body
  refine WP.seq (WP.mono (crtArgs_ok s h) ?_)
  rintro u ⟨hu, argsU, frameU, restU⟩
  refine WP.seq (WP.mono (crt_call v hu argsU) ?_)
  rintro z ⟨hz, frameZ, restZ, crt⟩
  refine WP.mono (check_ok v z hz) ?_
  rintro t ⟨_, status, bytes, cleared, frameT, restT⟩
  refine ⟨?_, cleared, (frameU.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide : 72 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)⟩)).trans
    ((frameZ.sub (calleeWrites_sub (crtWrites_sub h.valid))).trans frameT),
    (restU.mono (by simp)).trans ((restZ.mono (by simp [callClobbers])).trans restT)⟩
  have narrow : ((z.gpr .eax).setWidth 64).setWidth 32 = z.gpr .eax := by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have outcome := Rsa.outcome_eq (rc := (z.gpr .eax).setWidth 64)
    (r := Rsa.checkResult ((z.gpr .eax).setWidth 64) (bs 0) (bs 1) (bs 2)
      (Spec.Rsa.bytesAt z.mem (byteAddr g.temporary) g.length))
    (h.sources 0).length (h.sources 2).length (by rw [narrow]; exact crt) rfl bytes
  rw [status]
  exact outcome
end VG.Proof.Rsa.X86.PrivChecked
