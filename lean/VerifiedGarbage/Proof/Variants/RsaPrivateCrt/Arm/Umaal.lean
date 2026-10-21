module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm.Base
public import VerifiedGarbage.Proof.Bignum.Arm.CrtUmaal

/-!
# `vg_rsa_private_crt` on ARMv7 with `umaal`: the variant's code and proofs

The variant `VG.Variants.RsaPrivateCrt.Arm.Umaal.variant`
(`Variants/RsaPrivateCrt/Arm/Umaal.lean`): The shared integrated scanning round supplies
the windowed exponentiation; the shared UMAAL row transform supplies the
remaining arithmetic. The parameterized CRT proof retains the original contract,
checked with the baseline's `vg_rsa_public_precompute` and
`vg_rsa_public_precomputed_checked`.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.Arm.Umaal

open VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def variant : Proof.Rsa.Arm.CrtImpl :=
  { Base.variant with
    name := Spec.Rsa.privateCrtApi.name ++ "_umaal"
    code := CrtFios.code
    verified := crtUmaal_verified
    stack := by decide +kernel
    suffix := "_umaal"
    features := ["umaal"] }

end VG.Proof.Variants.RsaPrivateCrt.Arm.Umaal
