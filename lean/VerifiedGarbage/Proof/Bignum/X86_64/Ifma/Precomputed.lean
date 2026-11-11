module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Main
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Verified
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPreCT
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Main
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Verified
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPreCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_crt_ifma_precomputed` and `_ifma512_precomputed` on x86-64

`CrtIfma.codeP` is `CrtIfma.code` with `R² mod n` copied from the key's
precomputed values (`nSetupP`): correct (`codeP_correct`) and constant time
but for `n` and `pre`'s address (`codeP_constantTime`) against
`crtContractP`, from `CrtIfma.code`'s proofs of what follows the setup of
`n` (`mainBack_ok`, `dispatch_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Proof.Bignum.X86_64

theorem mainP_eq (l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (mul : Nat → Nat → Nat → Prog isa) : CrtIfma.mainP l2 mul =
    seqs ((nSetupP mul ++ primesSetup ++ checksP) ++
      (([.seq CrtIfma.anySizes (.ite .e (seqs (CrtIfma.pre mul ++ ([CrtIfma.ifmaAny l2] : List (Prog isa)) ++
        CrtIfma.post mul)) (seqs (qPhase mul (Crt.expLoop mul Crt.tabSelect) ++
          pPhase mul (Crt.expLoop mul Crt.tabSelect))))] : List (Prog isa)) ++ finish)) := by
  simp only [CrtIfma.mainP, List.append_assoc]

/-- `mainP`, for a valid modulus: as `main_ok`. -/
theorem mainP_ok {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (M : Mont) {s : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hp : PreR2 s B Z ((k + 7) / 8) (Spec.Rsa.os2ip nb))
    (hpq : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb)
    (hfront : (seqs (nSetupP M.mm ++ primesSetup ++ checksP)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpre : (seqs (CrtIfma.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm (CrtExpL.w4 M).code ++ pPhase M.mm (CrtExpL.w4 M).code)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (CrtIfma.mainP l2 M.mm) s (MainOut s B Z k op nb xb pb qb dpb dqb qib) := by
  rw [mainP_eq]
  exact wp_seqs_append (by simp [nSetupP]) (by simp) (WP.mono_mx hfront (frontP_ok M h hv hp hpq)
    fun t₀ ⟨minv, mp, mq, hr⟩ mx₀ => mainBack_ok h2 M h hv hr mx₀ hpre hpost hcrt)

/-- `vg_rsa_private_crt_ifma_precomputed` with Montgomery multiplication `M`,
given that the parts of its code outside the vector code never load MXCSR
(which the registration file evaluates). -/
theorem codeP_correct {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (M : Mont)
    (hfront : (seqs (nSetupP M.mm ++ primesSetup ++ checksP)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpre : (seqs (CrtIfma.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm (CrtExpL.w4 M).code ++ pPhase M.mm (CrtExpL.w4 M).code)).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : crtContractP.pre s) :
    ∃ t s', Exec isa (CrtIfma.codeP l2 M.mm) s t s' ∧ abiPreserved s s' ∧ crtContractP.post s s' := by
  obtain ⟨c, hv, hp, hpq⟩ := crtCtxP_of h
  clear h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa (CrtIfma.codeP l2 M.mm) s fun s' => (gprPreserved s s' ∧ crtContract.post s s') ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 by
    obtain ⟨t, s', he, ⟨hg, hp⟩, hmx⟩ := hwp
    exact ⟨t, s', he, ⟨hg.1, hg.2, hmx⟩, hp⟩
  unfold CrtIfma.codeP
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_mx (c := .block (Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] :
    List Instr))) (by decide +kernel) (crtHead_ok c) fun t₁ h₁ mx₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono_mx (by decide +kernel) (invalid_ok h₁.rdx h₁.rcx hk1 hk2
    (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi))
    (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ mx₂ => ?_
  have hpre' := crtPre_of c h₁ hm₂ k₂
  have kk := h₁.keep.trans k₂
  have hp₂ := hp.congr (by rw [hm₂]; exact h₁.inScr) (kk.gpr (by decide)) kk.2.1 kk.2.2
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [eval, hz₂]) (fun hb => ?_) (fun _ => ?_)
  · exact absurd hb (by rw [hv]; decide)
  · exact WP.mono (mainP_ok h2 M hpre' hv hp₂ hpq hfront hpre hpost hcrt) fun t ⟨⟨Mk, hp, hiff⟩, mx⟩ =>
      ⟨crtCode_fin c h₁ hm₂ k₂ hp (fun _ => ⟨hiff, rfl⟩) fun h => absurd h (by rw [hv]; decide),
        by rw [mx, mx₂, mx₁]⟩

/-! ## Constant time -/

/-- `mainP` leaks the same in runs that agree on the public data, the stack
pointer and `pre`'s address, given that its parts do. -/
theorem mainP_ct {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (M : Mont) (hS : SetupCT) (hC : ChecksPCT) (hQ : QPhaseCT M (CrtExpL.w4 M))
    (hP : PPhaseCT M (CrtExpL.w4 M))
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) (hR2 : RedcCT M Public.aR2)
    (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (StageP R0)) (CrtIfma.mainP l2 M.mm) fun _ _ => True := by
  rw [mainP_eq]
  refine RelCT.seqs_append (by simp [nSetupP]) (by simp) (RelCT.seq (frontP_ct M hS hC) ?_)
  refine RelCT.seqs_append (by simp) (by simp [finish]) (RelCT.seq ?_ hF)
  exact dispatch_ct h2 M hQ hP hR2 hXm hL hpost

variable (M : Mont)

/-- `vg_rsa_private_crt_ifma_precomputed` leaks the same in runs that agree
on the public data and `pre`'s address, given that `main`'s parts do. -/
theorem codeP_ct {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (hS : SetupCT) (hC : ChecksPCT) (hQ : QPhaseCT M (CrtExpL.w4 M))
    (hP : PPhaseCT M (CrtExpL.w4 M))
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) (hR2 : RedcCT M Public.aR2)
    (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two CCRelP) (CrtIfma.codeP l2 M.mm) fun _ _ => True := by
  unfold CrtIfma.codeP
  refine crtEntryWith_ct ccRelP_ok _ ?_
  exact (mainP_ct h2 M hS hC hQ hP hF hR2 hXm hL hpost).mono (fun _ _ h => two_bind (fun q t₁ t₂ h₁ h₂ =>
    ⟨(q.1.m, q.1.rsp, q.2), cc3P_stage h₁.1 h₁.2, cc3P_stage h₂.1 h₂.2⟩) h) fun _ _ h => h

/-- `vg_rsa_private_crt_ifma_precomputed` is constant time but for `n` and
`pre`'s address. -/
theorem codeP_constantTime {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    ConstantTime isa crtContractP.pre crtContractP.pub (CrtIfma.codeP l2 M.mm) := by
  have hct := codeP_ct M h2 setup_ct checksP_ct
    (qPhase_ct M (CrtExpL.w4 M) (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (CrtExpL.w4 M) (redc_ct_Y M) (CrtExpL.w4_ct M).2 (by taint_decide)))
    (pPhase_ct M (CrtExpL.w4 M) (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (CrtExpL.w4 M) (redc_ct_Y M) (CrtExpL.w4_ct M).1 (by taint_decide)) (redc_ct_X M) loadArr_ct_pI)
    crtFinish_ct (redc_ct_R2 M) (redc_ct_Xm M) loadArr_ct_pI hpost
  refine RelCT.constantTime (hct.mono
    (fun s₁ s₂ ⟨h₁, h₂, hp, h12, _, _⟩ => ⟨(ccPubOf s₁, stackArg s₁ 12), ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · obtain ⟨hr, a0, a1, a2, a3, a4, -, a6, -, a8, -, a10, a11, hn⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, ⟨r .rsp (by decide), a10.symm, by rw [← a11]; rfl, by rw [r .rcx (by decide)]; rfl,
      r .rdi (by decide), r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, a4.symm, a6.symm, a8.symm,
      by rw [← a1]; rfl, by rw [← a3]; rfl, hn.symm⟩, h12.symm⟩

end VG.Proof.Bignum.X86_64.Ifma
