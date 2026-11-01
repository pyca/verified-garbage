module
public import VerifiedGarbage.Proof.EcKey.AArch64.Lit
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothLit
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.P256
public import VerifiedGarbage.Spec.Ecdsa.P256

import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothContract
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJP
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombProduction
import VerifiedGarbage.Proof.P256.Order
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

/-- The pipelined comb's code: its addition scalar code storing within the
working space, apart from the tables its selection reads. -/
theorem booth_checks : JPChecks Impl.P256.CombArithmetic.K 8192 Impl.P256.Booth.mixed := by
  refine ⟨by decide, by decide, by decide, ?_, by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  · rw [Impl.P256.Booth.mixed_lit]; decide +kernel
  · rw [Impl.P256.Booth.mixed_lit]; decide +kernel

/-- The measured secret comb satisfies the existing scalar-multiplication interface. -/
theorem booth_comb_correct (hL : Law Spec.P256.curve) (hI : InvSounds)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    CombCorrect p256 Impl.P256.Booth.comb := by
  intro base k T s hs hm hf
  have hc := p256_ok hI
  exact WP.mono (tcombJP_ok (tcombLay hc.toBaseCfgOk) (combA hc.toBaseCfgOk)
    ((Forward.CombArithmetic.compiler_correct (by decide)).on _ _)
    (fun _ h => absurd h List.not_mem_nil) (by decide) hL hc.am3 hc.onG
    (tcombVals hc.toBaseCfgOk hL hT) hc.p_lt (by decide) (Proof.P256.booth hL) hf.k_lt
    Impl.P256.Booth.program_mixed booth_checks hs hm hf)
    fun _ ⟨K, U, M, L, R⟩ => ⟨K, U.mono fun w hw => List.mem_append_left _ hw, M, L, R⟩

theorem booth_sign_verified (hL : Law Spec.P256.curve) (hI : InvSounds)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    Verified AArch64.target Impl.P256.Booth.sign
      (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P256.inst (AArch64.abi.withConsts p256.combConsts)) :=
  booth_sign_verified_of_comb hL hI (booth_comb_correct hL hI hT)

end VG.Proof.Ecdsa.AArch64

namespace VG.Proof.EcKey.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

theorem booth_pk_verified (hL : Law Spec.P256.curve) (hI : InvSounds)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    Verified AArch64.target Impl.P256.Booth.publicKey
      (Spec.EcKey.P256.inst.publicKeyContract (AArch64.abi.withConsts p256.combConsts)) :=
  booth_pk_verified_of_comb hL hI (Ecdsa.AArch64.booth_comb_correct hL hI hT)

end VG.Proof.EcKey.AArch64
