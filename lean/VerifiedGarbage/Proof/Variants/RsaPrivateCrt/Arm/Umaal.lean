module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm.Base
public import VerifiedGarbage.Proof.Bignum.Arm.CrtUmaal
import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
import VerifiedGarbage.Proof.Framework.Lit
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

/-- The stack of both functions before the row transform, which does not add to it
(`armStack_umaalArithmetic`), in one evaluation: the kernel neither builds the transformed code
nor builds twice the code the two share. -/
theorem stacks : FrameStack.armStack (CrtFn.codeWith CrtFios.phase) ≤ 56 ∧
    FrameStack.armStack (CrtFn.codeGiven CrtFios.phase) ≤ 56 := by
  decide +kernel

def variant : Proof.Rsa.Arm.CrtImpl :=
  { Base.variant with
    name := "vg_rsa_private_crt" ++ "_umaal"
    code := CrtFios.code
    verified := crtUmaal_verified
    stack := (armStack_umaalArithmetic _).trans stacks.1
    crtPName := "vg_rsa_private_crt_precomputed" ++ "_umaal"
    crtP := CrtFios.codeGiven
    crtPVerified := crtUmaal_verifiedP
    crtPStack := (armStack_umaalArithmetic _).trans stacks.2
    crtPNoIcall := by lit_decide
    pcName := Spec.Rsa.publicPrecomputeApi.name ++ "_umaal"
    pc := umaalArithmetic Base.variant.pc
    pcVerified := umaalArithmetic_verified Base.variant.pcVerified
    pcStack := (armStack_umaalArithmetic _).trans Base.variant.pcStack
    pcNoIcall := by lit_decide
    pdName := "vg_rsa_public_precomputed_checked" ++ "_umaal"
    pd := umaalArithmetic Base.variant.pd
    pdVerified := umaalArithmetic_verified Base.variant.pdVerified
    pdStack := (armStack_umaalArithmetic _).trans Base.variant.pdStack
    pdNoIcall := by lit_decide
    suffix := "_umaal"
    features := ["umaal"] }

end VG.Proof.Variants.RsaPrivateCrt.Arm.Umaal
