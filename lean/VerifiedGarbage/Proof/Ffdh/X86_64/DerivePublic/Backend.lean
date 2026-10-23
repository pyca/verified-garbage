module

public import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Safety
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Verified
import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Contract
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Safety
meta import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
meta import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Verified
meta import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Template
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Verify FFDH public-value derivation for every Montgomery backend -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

theorem deriveInline_verified (v : RoundImpl) : Verified target (deriveInline v)
    (Spec.Ffdh.derivePublicContract abi) := by
  apply dv_verified v.mont (CrtExpL.w4 v.mont) (R2Impl.words v.mont) _ (deriveInline_mx v)
  exact two_map id (fun _ _ h => h.1)
    (crtExpLoop_ct v.mont CrtSel.sse CrtSel.sse_ct (by taint_decide))

theorem dvSatisfiable8 : ∃ s, (Spec.Ffdh.derivePublicContract abi 8).pre s := by
  sig_implies_sat [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, stackArgs_three, List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
    [dvSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using dvSat

/-- With calls of `v.mm`, which need 8 bytes of stack for the return address. -/
theorem deriveCode_verified (v : RoundImpl) : Verified target (deriveCode v)
    (Spec.Ffdh.derivePublicContract abi 8) := by
  have hv := deriveInline_verified v
  rw [← deriveCode_inline] at hv
  refine Verified.of_inline_verified (deriveCode_inlineOk v) hv
    ((Contract.Implies.refl hv.2.2).stack8_abi dvSatisfiable8) (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u hs hp => ?_) (fun _ _ _ _ h => Sig.rsp_of_pub h)
  obtain ⟨-, -, hw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hyl, -, -, -⟩ :=
    dv_implies.pre s (Sig.pre_stack0_abi hs)
  have hy := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := (s.gpr .rsi).toNat)
    (by rw [hw]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt)
  rw [hyl] at hy
  sig_post [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, stackArgs_three, List.append_eq] at hp ⊢
  rw [bytesAt_overlay hy]
  exact hp

end VG.Proof.Ffdh.X86_64.DerivePublic
