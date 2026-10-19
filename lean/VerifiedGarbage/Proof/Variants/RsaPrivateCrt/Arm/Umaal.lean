module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm.Base
public import VerifiedGarbage.Proof.Bignum.Arm.CrtUmaal

/-!
# `vg_rsa_private_crt` on ARMv7 with `umaal`: the variant's code and proofs

The variant `VG.Variants.RsaPrivateCrt.Arm.Umaal.variant`
(`Variants/RsaPrivateCrt/Arm/Umaal.lean`): the baseline's code with each
row by `rowU` (`umaalRows`), whose proofs are the baseline's
(`umaalRows_verified`), checked with the baseline's
`vg_rsa_public_precompute` and `vg_rsa_public_precomputed_checked`.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.Arm.Umaal

open VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def variant : Proof.Rsa.Arm.CrtImpl :=
  { Base.variant with
    name := Spec.Rsa.privateCrtApi.name ++ "_umaal"
    code := umaalRows CrtFn.code
    verified := crtUmaal_verified
    stack := (armStack_umaalRows _).trans Base.variant.stack
    suffix := "_umaal"
    features := ["umaal"] }

end VG.Proof.Variants.RsaPrivateCrt.Arm.Umaal
