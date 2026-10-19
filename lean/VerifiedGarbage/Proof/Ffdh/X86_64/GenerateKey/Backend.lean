module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Safety
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Verified
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Contract
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Safety
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Verified
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Template
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Verify FFDH key-generation attempts for every Montgomery backend -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

theorem generateInline_verified (v : RoundImpl) : Verified target (generateInline v)
    (Spec.Ffdh.generateKeyContract abi) := by
  apply gk_verified v.mont (CrtExpL.w4 v.mont) (R2Impl.words v.mont) _ (generateInline_mx v)
  exact two_map id (fun _ _ h => h.1)
    (crtExpLoop_ct v.mont CrtSel.sse CrtSel.sse_ct (by taint_decide))

theorem gkSatisfiable8 : ∃ s, (Spec.Ffdh.generateKeyContract abi 8).pre s := by
  sig_implies_sat [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, stackArgs_five, List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
    [gkSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using gkSat

/-- With calls of `v.mm`, which need 8 bytes of stack for the return address. -/
theorem generateCode_verified (v : RoundImpl) : Verified target (generateCode v)
    (Spec.Ffdh.generateKeyContract abi 8) := by
  have hv := generateInline_verified v
  rw [← generateCode_inline] at hv
  refine Verified.of_inline_verified (generateCode_inlineOk v) hv
    ((Contract.Implies.refl hv.2.2).stack8_abi gkSatisfiable8) (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u hs hp => ?_) (fun _ _ _ _ h => Sig.rsp_of_pub h)
  obtain ⟨-, -, hw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hxl, hyl, -, -⟩ :=
    gk_implies.pre s (Sig.pre_stack0_abi hs)
  have hx := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := (s.gpr .rsi).toNat)
    (by rw [hw]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt)
  have hy := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := (s.gpr .rcx).toNat)
    (by rw [hw]; simp) (Nat.le_of_lt (s.gpr .rcx).isLt)
  rw [hxl] at hx
  rw [hyl] at hy
  sig_post [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, stackArgs_five, List.append_eq] at hp ⊢
  rw [bytesAt_overlay hx, bytesAt_overlay hy]
  exact hp

end VG.Proof.Ffdh.X86_64.GenerateKey
