module

public import VerifiedGarbage.Proof.EcKey.Arm.P224.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration

/-! # P-224 public keys (FIPS 186-5 §A.2) on 32-bit ARM -/

@[expose] public section

namespace VG.Generic.P224.Arm.EcP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.EcKey.P224.publicKeyApi.artifact Arm.target {
    consts := Impl.Weierstrass.Arm.p224CombConsts
    code := Impl.Ecdsa.Arm.publicKeyP224Comb
    verified := Proof.EcKey.Arm.P224.combPk_verified h.law },
  Spec.EcKey.P224.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    consts := Impl.Weierstrass.Arm.p224CombConsts
    code := Impl.Ecdsa.Arm.publicKeyP224CombU
    verified := Proof.EcKey.Arm.P224.combPkU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P224.Arm.EcP224
