module

import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Terms
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CrtImplies
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
meta import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtImplies
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Rsa.Contract

/-!
# `vg_rsa_private_crt_ifma` on x86-64, any size: verified against the shared contract

`code` is `Crt.code` with
`CrtIfma.main` (`main_ct`), so the function is constant time but for `n`
(`code_constantTime`); with correctness (`code_correct`) and the contract on
the registers and the stack (`crt_implies`), `CrtIfma.code` is constant
time (`code_constantTime`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Proof.Bignum.X86_64 (CCRel CC3 CCPub cc3_pre crtEntryWith_ct ccRel_ok two_bind ccPubOf
  SetupCT ChecksCT QPhaseCT PPhaseCT RedcCT LoadCT Stage R0 R5 setup_ct checks_ct qPhase_ct pPhase_ct unit_ct
  gPow_ct_Q gPow_ct_P redc_ct_Y redc_ct_X redc_ct_R2 redc_ct_Xm pow_ct expLoop_ct_Q expLoop_ct_P loadArr_ct_pI
  crtFinish_ct crt_implies)

variable (M : Mont)

/-- `vg_rsa_private_crt_ifma` leaks the same in runs that agree on the public
data, given that `main`'s parts do. -/
theorem code_ct {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M (CrtExpL.w4 M)) (hP : PPhaseCT M (CrtExpL.w4 M))
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) (hR2 : RedcCT M Public.aR2)
    (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two CCRel) (CrtIfma.code l2 M.mm) fun _ _ => True := by
  unfold CrtIfma.code
  refine crtEntryWith_ct ccRel_ok _ ?_
  have toM : ∀ p t, CC3 p t ∧ isa.eval .ne t = some false → Stage R0 p.m t := by
    rintro p t ⟨h, he⟩
    obtain ⟨xb, pb, qb, dpb, dqb, qib, hpre⟩ := cc3_pre h
    obtain ⟨_, _, _, _, _, _, hz⟩ := h
    have hv : Spec.Rsa.modulusValid p.m.N p.m.k = true := by
      simp only [eval, hz] at he; simpa using he
    exact ⟨t, xb, pb, qb, dpb, dqb, qib, hpre, hv, rfl⟩
  exact (main_ct h2 M hS hC hQ hP hF hR2 hXm hL hpost).mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ =>
    ⟨p.m, toM p t₁ h₁, toM p t₂ h₂⟩) h) fun _ _ h => h

/-- `vg_rsa_private_crt_ifma` is constant time but for `n`. -/
theorem code_constantTime_of {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M (CrtExpL.w4 M)) (hP : PPhaseCT M (CrtExpL.w4 M))
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) (hR2 : RedcCT M Public.aR2)
    (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    ConstantTime isa crtContract.pre crtContract.pub (CrtIfma.code l2 M.mm) := by
  refine RelCT.constantTime ((code_ct M h2 hS hC hQ hP hF hR2 hXm hL hpost).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨ccPubOf s₁, ?_, ?_⟩)
    fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, a0, a1, a2, a3, a4, -, a6, -, a8, -, a10, a11, hn⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, r .rsp (by decide), a10.symm, by rw [← a11]; rfl, by rw [r .rcx (by decide)]; rfl,
      r .rdi (by decide), r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, a4.symm, a6.symm, a8.symm,
      by rw [← a1]; rfl, by rw [← a3]; rfl, hn.symm⟩

section

/-- `vg_rsa_private_crt_ifma` is constant time but for `n`. -/
theorem code_constantTime {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (M : Mont)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    ConstantTime isa crtContract.pre crtContract.pub (CrtIfma.code l2 M.mm) :=
  code_constantTime_of M h2 setup_ct checks_ct
    (qPhase_ct M (CrtExpL.w4 M) (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (CrtExpL.w4 M) (redc_ct_Y M) (CrtExpL.w4_ct M).2 (by taint_decide)))
    (pPhase_ct M (CrtExpL.w4 M) (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (CrtExpL.w4 M) (redc_ct_Y M) (CrtExpL.w4_ct M).1 (by taint_decide)) (redc_ct_X M) loadArr_ct_pI)
    crtFinish_ct (redc_ct_R2 M) (redc_ct_Xm M) loadArr_ct_pI hpost

end

end VG.Proof.Bignum.X86_64.Ifma
