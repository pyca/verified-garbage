module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Safety
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Verified
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Contract
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Safety
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Verified
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Template
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Verify FFDH exchange for every Montgomery backend -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

theorem exchangeInline_verified (v : RoundImpl) : Verified target (exchangeInline v)
    (Spec.Ffdh.exchangeContract abi) := by
  apply ex_verified v.mont (CrtExpL.w4 v.mont) (R2Impl.words v.mont) _ (exchangeInline_mx v)
  exact two_map id (fun _ _ h => h.1)
    (crtExpLoop_ct v.mont CrtSel.sse CrtSel.sse_ct (by taint_decide))

theorem exSatisfiable8 : ∃ s, (Spec.Ffdh.exchangeContract abi 8).pre s := by
  sig_implies_sat [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, stackArgs_five, List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
    [exSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using exSat

/-- With calls of `v.mm`, which need 8 bytes of stack for the return address. -/
theorem exchangeCode_verified (v : RoundImpl) : Verified target (exchangeCode v)
    (Spec.Ffdh.exchangeContract abi 8) := by
  have hv := exchangeInline_verified v
  rw [← exchangeCode_inline] at hv
  refine Verified.of_inline_verified (exchangeCode_inlineOk v) hv
    ((Contract.Implies.refl hv.2.2).stack8_abi exSatisfiable8) (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u hs hp => ?_) (fun _ _ _ _ h => Sig.rsp_of_pub h)
  have hw : s.wr = _ := (ex_implies.pre s (Sig.pre_stack0_abi hs)).2.2.1
  have hb := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := (s.gpr .rsi).toNat)
    (by rw [hw]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt)
  sig_post [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, stackArgs_five, List.append_eq] at hp ⊢
  intro h₁ h₂
  rw [written_overlay hb]
  exact hp h₁ h₂

end VG.Proof.Ffdh.X86_64.Exchange
