module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm.Base
public import VerifiedGarbage.Proof.Bignum.Arm.CrtUmaal
import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
public meta import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic

/-!
# `vg_rsa_private_crt` on ARMv7 with `umaal`: the variant's code and proofs

The variant `VG.Variants.RsaPrivateCrt.Arm.Umaal.variant`
(`Variants/RsaPrivateCrt/Arm/Umaal.lean`): The shared integrated scanning round supplies
the windowed exponentiation; the shared UMAAL row transform supplies the
remaining arithmetic. The parameterized CRT proof retains the original contract,
checked with the associated UMAAL public precomputation and operation. Public
precomputation uses the normalized R-squared shortcut with the original fallback.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.Arm.Umaal

open VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def variant : Proof.Rsa.Arm.CrtImpl :=
  { Base.variant with
    name := "vg_rsa_private_crt" ++ "_umaal"
    code := CrtFios.code
    verified := crtUmaal_verified
    stack := by decide +kernel
    pcName := Spec.Rsa.publicPrecomputeApi.name ++ "_umaal"
    pc := umaalArithmetic Base.variant.pc
    pcVerified := umaalArithmetic_verified Base.variant.pcVerified
    pcStack := (armStack_umaalArithmetic _).trans Base.variant.pcStack
    pdName := Spec.Rsa.publicPrecomputedCheckedApi.name ++ "_umaal"
    pd := umaalArithmetic Base.variant.pd
    pdVerified := umaalArithmetic_verified Base.variant.pdVerified
    pdStack := (armStack_umaalArithmetic _).trans Base.variant.pdStack
    suffix := "_umaal"
    features := ["umaal"] }

end VG.Proof.Variants.RsaPrivateCrt.Arm.Umaal
