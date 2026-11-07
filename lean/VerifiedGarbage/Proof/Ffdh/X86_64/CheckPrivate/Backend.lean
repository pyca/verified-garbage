module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Safety
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Verified
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Contract
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Safety
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Verified
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Template
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Verify FFDH private-key validation for every Montgomery backend -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.X86_64

theorem privateInline_verified (v : RoundImpl) (e : ExpImpl) : Verified target (privateInline v e)
    (Spec.Ffdh.checkPrivateContract abi) := by
  have h := kp_verified v.mont (e.E v.mont) (R2Impl.words v.mont) (e.ctX v.mont)
  rw [e.code_eq] at h
  exact h (privateInline_ctl v e)

theorem kpSatisfiable8 : ∃ s, (Spec.Ffdh.checkPrivateContract abi 8).pre s := by
  sig_implies_sat [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, stackArgs_three, List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
    [kpSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using kpSat

/-- With calls of `v.mm`, which need 8 bytes of stack for the return address. -/
theorem privateCode_verified (v : RoundImpl) (e : ExpImpl) : Verified target (privateCode v e)
    (Spec.Ffdh.checkPrivateContract abi 8) := by
  have hv := privateInline_verified v e
  rw [← privateCode_inline v e] at hv
  refine Verified.of_inline_verified (privateCode_inlineOk v e) hv
    ((Contract.Implies.refl hv.2.2).stack8_abi kpSatisfiable8) (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u hs hp => ?_) (fun _ _ _ _ h => Sig.rsp_of_pub h)
  sig_post [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, stackArgs_three, List.append_eq] at hp ⊢
  exact hp

end VG.Proof.Ffdh.X86_64.CheckPrivate
