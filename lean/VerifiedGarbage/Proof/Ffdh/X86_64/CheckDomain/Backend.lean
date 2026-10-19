module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Safety
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Verified
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Contract
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Safety
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Verified
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Template
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Verify FFDH domain validation for every Montgomery backend -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

theorem domainInline_verified (v : RoundImpl) : Verified target (domainInline v)
    (Spec.Ffdh.checkDomainContract abi) := by
  apply cd_verified v.mont (CrtExpL.w4 v.mont) (R2Impl.words v.mont) _ (domainInline_mx v)
  exact two_map id (fun _ _ h => h.1)
    (crtExpLoop_ct v.mont CrtSel.sse CrtSel.sse_ct (by taint_decide))

theorem cdSatisfiable8 : ∃ s, (Spec.Ffdh.checkDomainContract abi 8).pre s := by
  sig_implies_sat [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, List.append_eq,
    Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] [cdSat] using cdSat

/-- With calls of `v.mm`, which need 8 bytes of stack for the return address. -/
theorem domainCode_verified (v : RoundImpl) : Verified target (domainCode v)
    (Spec.Ffdh.checkDomainContract abi 8) := by
  have hv := domainInline_verified v
  rw [← domainCode_inline] at hv
  refine Verified.of_inline_verified (domainCode_inlineOk v) hv
    ((Contract.Implies.refl hv.2.2).stack8_abi cdSatisfiable8) (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u _ hp => ?_) (fun _ _ _ _ h => Sig.rsp_of_pub h)
  sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, List.append_eq] at hp ⊢
  exact hp

end VG.Proof.Ffdh.X86_64.CheckDomain
