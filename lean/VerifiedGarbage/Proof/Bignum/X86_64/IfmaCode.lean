import VerifiedGarbage.Proof.Bignum.X86_64.IfmaMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCode

/-!
# RSA with AVX512_IFMA on x86-64: correctness

`CrtIfma.code`, from a state `crtContract` allows, writes `privateCrt` of
its inputs (`ifmaCode_correct`), as `Crt.code` does. Unlike `Crt.code`, it
loads MXCSR (around the vector code), so the calling convention's MXCSR
bits are tracked through it rather than read off the code.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- `vg_rsa_private_crt_ifma` with Montgomery multiplication `M`, given that
the parts of its code outside the vector code never load MXCSR (which the
registration file evaluates). -/
theorem ifmaCode_correct (M : Mont)
    (hfront : (seqs (nSetup M.mm ++ primesSetup ++ checks)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpre : (seqs (CrtIfma.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm ++ pPhase M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : crtContract.pre s) :
    ∃ t s', Exec isa (CrtIfma.code M.mm) s t s' ∧ abiPreserved s s' ∧ crtContract.post s s' := by
  have c := crtCtx_of h
  clear h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa (CrtIfma.code M.mm) s fun s' => (gprPreserved s s' ∧ crtContract.post s s') ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 by
    obtain ⟨t, s', he, ⟨hg, hp⟩, hmx⟩ := hwp
    exact ⟨t, s', he, ⟨hg.1, hg.2, hmx⟩, hp⟩
  unfold CrtIfma.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_mx (c := .block (Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] :
    List Instr))) (by decide +kernel) (crtHead_ok c) fun t₁ h₁ mx₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono_mx (by decide +kernel) (invalid_ok h₁.rdx h₁.rcx hk1 hk2
    (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi))
    (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ mx₂ => ?_
  have hpre' := crtPre_of c h₁ hm₂ k₂
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false := by simpa using hb
    exact WP.mono_mx (by decide +kernel) (fail_ok hpre'.scr hpre'.rdi (by omega)
      (by omega) (by omega) hpre'.hO hpre'.hK hpre'.out hpre'.outSep)
      fun t hp mx => ⟨crtCode_fin c h₁ hm₂ k₂ hp (fun h => absurd h (by rw [hv]; decide)) fun _ => ⟨rfl, rfl⟩,
        by rw [mx, mx₂, mx₁]⟩
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true := by simpa using hb
    exact WP.mono (ifmaMain_ok M hpre' hv (fun hw hp hq => by
      unfold offQ slot wsWords hdrBytes tabBytes CrtIfma.D at *; omega)
      hfront hpre hpost hcrt) fun t ⟨⟨Mk, hp, hiff⟩, mx⟩ =>
      ⟨crtCode_fin c h₁ hm₂ k₂ hp (fun _ => ⟨hiff, rfl⟩) fun h => absurd h (by rw [hv]; decide),
        by rw [mx, mx₂, mx₁]⟩

end VG.Proof.Bignum.X86_64
