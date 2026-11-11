module

public import VerifiedGarbage.Proof.Rsa.X86.PrivP.Call
public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl
import VerifiedGarbage.Proof.Rsa.X86.PrivCheck
import VerifiedGarbage.Proof.Rsa.X86.PrivRetained
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_private_checked_precomputed` on x86: the body

`vg_rsa_private_checked`'s, with `vg_rsa_private_crt_precomputed` called in
place of `vg_rsa_private_crt` (`privateBodyP_ok`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem privateBodyP_ok (v : CrtImpl) (w : CrtPImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} {P : BitVec 32}
    {L : Nat} (s : State) (h : PrivContext g bs s) (H : PreCtx g bs P L s) :
    WP isa (bodyP w.name w.code v.pcName v.pc v.pdName v.pd) s fun t =>
      Spec.Rsa.writtenOutcome t.mem (byteAddr g.output) g.length (t.gpr .eax)
        (Spec.Rsa.privateChecked (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7)) ∧
      Spec.Rsa.bytesAt t.mem (byteAddr g.temporary) g.length = List.replicate g.length 0 ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  unfold bodyP
  refine WP.seq (WP.mono (crtArgsP_ok s h H) ?_)
  rintro u ⟨hu, Hu, argsU, frameU, restU⟩
  refine WP.seq (WP.mono (crtP_call w hu Hu argsU) ?_)
  rintro z ⟨hz, _, frameZ, restZ, crt⟩
  refine WP.mono (check_ok v z hz) ?_
  rintro t ⟨_, status, bytes, cleared, frameT, restT⟩
  refine ⟨?_, cleared, (frameU.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide : 80 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)⟩)).trans
    ((frameZ.sub (calleeWrites_sub (crtWritesP_sub h.valid))).trans frameT),
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
