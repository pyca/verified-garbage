module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm.Base
public import VerifiedGarbage.Proof.Bignum.Arm.CrtUmaal
import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
public import VerifiedGarbage.Proof.Rsa.Arm.PublicUmaal

/-!
# `vg_rsa_private_crt` on ARMv7 with `umaal`: the variant's code and proofs

The variant `VG.Variants.RsaPrivateCrt.Arm.Umaal.variant`
(`Variants/RsaPrivateCrt/Arm/Umaal.lean`): The shared integrated scanning round supplies
the windowed exponentiation; the shared UMAAL row transform supplies the
remaining arithmetic. The parameterized CRT proof retains the original contract,
checked with the associated UMAAL public precomputation and operation.
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
    pcName := Spec.Rsa.publicPrecomputeApi.name ++ "_umaal"
    pc := umaalArithmetic PcFn.code
    pcVerified := Proof.Rsa.Arm.precompute_umaal_verified
    pcStack := Proof.Rsa.Arm.precompute_umaal_stack
    pdName := Spec.Rsa.publicPrecomputedCheckedApi.name ++ "_umaal"
    pd := umaalArithmetic PdFn.code
    pdVerified := Proof.Rsa.Arm.public_precomputed_umaal_verified
    pdStack := Proof.Rsa.Arm.public_precomputed_umaal_stack
    suffix := "_umaal"
    features := ["umaal"] }

end VG.Proof.Variants.RsaPrivateCrt.Arm.Umaal
