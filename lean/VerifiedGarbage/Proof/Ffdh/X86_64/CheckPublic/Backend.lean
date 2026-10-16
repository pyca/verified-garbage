module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Safety
public import VerifiedGarbage.Spec.Ffdh.Contract
public meta import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Verified
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Contract
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSelV
import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Verify FFDH public-key validation for every Montgomery backend -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

theorem publicInline_verified (v : RoundImpl) : Verified target (publicInline v)
    (Spec.Ffdh.checkPublicContract abi) := by
  apply cp_verified v.mont (CrtExpL.w4 v.mont) (R2Impl.words v.mont) _ (publicInline_mx v)
  exact two_map id (fun _ _ h => h.1)
    (crtExpLoop_ct v.mont CrtSel.sse CrtSel.sse_ct (by taint_decide))

theorem cpSatisfiable8 : ∃ s, (Spec.Ffdh.checkPublicContract abi 8).pre s := by
  sig_implies_sat [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, stackArgs_one, List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
    [cpSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using cpSat

/-- With calls of `v.mm`, which need 8 bytes of stack for the return address. -/
theorem publicCode_verified (v : RoundImpl) : Verified target (publicCode v)
    (Spec.Ffdh.checkPublicContract abi 8) := by
  have hv := publicInline_verified v
  rw [← publicCode_inline] at hv
  refine Verified.of_inline_verified (publicCode_inlineOk v) hv
    ((Contract.Implies.refl hv.2.2).stack8_abi cpSatisfiable8) (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u hs hp => ?_) (fun _ _ _ _ h => Sig.rsp_of_pub h)
  sig_post [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, stackArgs_one, List.append_eq] at hp ⊢
  exact hp

end VG.Proof.Ffdh.X86_64.CheckPublic
