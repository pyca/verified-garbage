module

public import VerifiedGarbage.Proof.Rsa.X86_64.RpCode
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedMain
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.X86_64.CvCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86_64.RpOut
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverFolded
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Rsa.RecoverFolded
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.TCB.Artifact

/-! # Functional correctness against the unchanged recovery contract -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

open VG.Impl.Rsa.X86_64.Keys.Recover.Folded

theorem rpCode_correct [InvLaw] (M : Mont) (hmx : (Folded.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : rpContract.pre s) :
    ∃ t s', Exec isa (Folded.code M.mm) s t s' ∧ abiPreserved s s' ∧ rpContract.post s s' := by
  have c := rpCtx_of h
  clear h
  have hk1 : 64 ≤ (s.gpr .r9).toNat := c.L.k1
  have hk2 : (s.gpr .r9).toNat ≤ 1024 := c.L.k2
  suffices hwp : WP isa (Folded.code M.mm) s fun s' => gprPreserved s s' ∧ rpContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold Folded.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rpHead_ok' c) fun t₁ h₁ => ?_
  have hnb₁ := c.n.congrK h₁.inScr h₁.keep
  have hnl : (rpIn s).nb.length = (s.gpr .r9).toNat := bytesAt_length _ _ _
  refine WP.mono (invalid_ok h₁.rdx h₁.rcx hk1 hk2 hnl (fun i hi => hnb₁.rd i (by rw [hnl]; exact hi))
    (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  have hpre := rpPre_of c h₁ hm₂ k₂
  have hsp₂ : t₂.gpr .rsp = s.gpr .rsp := hpre.rsp
  refine WP.ite (!Spec.Rsa.modulusValid (rpIn s).N (s.gpr .r9).toNat) (by simp [eval, hz₂]) (fun hb => ?_)
    (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (rpIn s).N (s.gpr .r9).toNat = false := by simpa using hb
    have z : 128 * (s.gpr .r9).toNat ≤ (stackArg s 5).toNat * 8 := c.L.z
    exact WP.mono (rpFail_ok hpre.scr hpre.rdi (show 8 * 32 ≤ (stackArg s 5).toNat * 8 by omega) hpre.args
      (show 1 ≤ (s.gpr .r9).toNat by omega) (show (s.gpr .r9).toNat < 2 ^ 31 by omega) hpre.oP hpre.oQ hpre.a)
      fun t ⟨z1, z2, hax, hsv, hfr, hsp⟩ => ⟨rpGpr_of c hsv hsp hsp₂ fun x hx n1 n2 => by
        rw [hfr x n1 n2, hm₂]; exact h₁.inScr x hx, by
        show Spec.Rsa.writtenAll _ _ _ _
        have hnone : (Spec.Rsa.primesKey (rpIn s).nb (rpIn s).eb (rpIn s).db).1 = none := by
          simp only [Spec.Rsa.primesKey]
          rw [hnl, hv]; simp
        simp only [rpIn] at hnone
        rw [hnone, hax]
        simp only [Option.map_none, Spec.Rsa.writtenAll, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        exact ⟨rfl, bytesAt_zero z1, bytesAt_zero z2⟩⟩
  · have hv : Spec.Rsa.modulusValid (rpIn s).N (s.gpr .r9).toNat = true := by simpa using hb
    exact WP.mono (rpMain_ok M hpre hv) fun t ⟨res, hres, b1, b2, hax, hsv, hfr, hsp⟩ =>
      ⟨rpGpr_of c hsv hsp hsp₂ fun x hx n1 n2 => by
        rw [hfr x hx n1 n2, hm₂]; exact h₁.inScr x hx, by
        have := rpWritten_of (m := t.mem) (pp := s.gpr .rdi) (pq := s.gpr .rdx) (eb := (rpIn s).eb)
          (db := (rpIn s).db) (by rw [hnl]; exact hv) hres (by rw [hnl]; exact b1) (by rw [hnl]; exact b2) hax
        rw [hnl] at this
        exact this⟩

end VG.Proof.Rsa.X86_64.RecoveryFolded
