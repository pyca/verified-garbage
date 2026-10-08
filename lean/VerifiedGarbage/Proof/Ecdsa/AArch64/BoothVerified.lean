import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothContract
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombProduction
import VerifiedGarbage.Proof.P256.Order

namespace VG.Proof.Ecdsa.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

/-- The measured secret comb satisfies the existing scalar-multiplication interface. -/
theorem booth_comb_correct (hL : Law Spec.P256.curve) (hI : InvSounds)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    CombCorrect p256 Impl.P256.Booth.comb := by
  intro base k T s hs hm hf
  have hc := p256_ok hI
  exact tcombJWith_ok (tcombLay hc) (combA hc)
    (Forward.CombArithmetic.compiler_correct (by decide)) (by decide) hL hc.am3 hc.onG
    (tcombVals hc hL hT) hc.p_lt (by decide) (Proof.P256.booth hL) hf.k_lt hs hm hf

theorem booth_sign_verified (hL : Law Spec.P256.curve) (hI : InvSounds)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    Verified AArch64.target Impl.P256.Booth.sign
      (Spec.Ecdsa.P256.inst.signContract (AArch64.abi.withConsts p256.combConsts)) :=
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
