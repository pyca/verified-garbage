module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.DecompressMain
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Candidate
import VerifiedGarbage.Proof.Weierstrass.Sqrt
public import VerifiedGarbage.Spec.EcKey.P256
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Ecdh.AArch64.P256.CheckVerified
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
meta import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
meta import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Contract

/-! # Instantiate shared compression with P256's field configuration -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64.P256Decompress

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64

abbrev code : Prog isa := Impl.EcKey.Compressed.AArch64.decompress p256

materialize_shared baseline := code

 theorem ct : ConstantTime isa (decompressContract Spec.P256.curve Impl.EcKey.Compressed.rootThreeModFour).pre
    (decompressContract Spec.P256.curve Impl.EcKey.Compressed.rootThreeModFour).pub code := by
  apply VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2])
  · intro s₁ s₂ _ _ hp
    obtain ⟨hsp, hout, hpk, hws⟩ := hp
    refine ⟨hsp, ?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hout
    · exact hpk
    · exact hws
  · taint_decide

 theorem sat : ∃ s, (Spec.EcKey.P256.inst.decompressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P256.curve.len = 32 := rfl
  sig_implies_sat [Spec.EcKey.P256.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState 32)

 theorem chain_ok : Proof.Weierstrass.AArch64.ChainOk
    (Impl.EcKey.Compressed.AArch64.rootChain p256 ((p256.C.p + 1) / 4)) ((p256.C.p + 1) / 4) := by
  apply Proof.Weierstrass.AArch64.ChainOk.of_check
  decide +kernel

 theorem verified (hL : Proof.Weierstrass.Law Spec.P256.curve)
    (hI : Proof.Weierstrass.AArch64.InvSounds) :
    Verified target code (Spec.EcKey.P256.inst.decompressPublicKeyContract abi 0) := by
  have hc := (p256_ok hI).toBaseCfgOk
  exact Verified.of_correct (decompress_correct p256 hc _
    (candidateThree_correct hc (by decide +kernel) chain_ok)
    (by lit_decide) (by lit_decide) (by lit_decide)) ct
    (decompress_implies Spec.EcKey.P256.inst _
      (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel)) sat)

end VG.Proof.EcKey.Compressed.AArch64.P256Decompress
