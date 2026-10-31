module

public import VerifiedGarbage.Proof.EcKey.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-384 public keys (FIPS 186-5 §A.2) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.Arm.EcP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.EcKey.P384.publicKeyApi.artifact Arm.target {
    consts := Impl.Weierstrass.Arm.p384CombConsts
    code := Impl.Ecdsa.Arm.publicKeyP384Comb
    verified := Proof.EcKey.Arm.P384.combPk_verified h.law },
  Spec.EcKey.P384.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    consts := Impl.Weierstrass.Arm.p384CombConsts
    code := Impl.Ecdsa.Arm.publicKeyP384CombU
    verified := Proof.EcKey.Arm.P384.combPkU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P384.Arm.EcP384
