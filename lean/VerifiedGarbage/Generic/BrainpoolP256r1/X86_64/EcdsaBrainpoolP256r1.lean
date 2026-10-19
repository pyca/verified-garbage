module

import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.BrainpoolP256r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP256r1

/-! # brainpoolP256r1 on x86-64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.X86_64.EcdsaBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.Ecdsa.BrainpoolP256r1.signApi.artifact X86_64.target {
    notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication calls `vg_brainpoolp256r1_mul`, a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), which hold for any `a`. \
      Inversions use divsteps, by calls of `vg_brainpoolp256r1_inv_mod_p` and `vg_brainpoolp256r1_inv_mod_n`. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.Ecdsa.X86_64.signBrainpoolP256r1
    stack := 8
    verified := Proof.Ecdsa.X86_64.BrainpoolP256r1.sign_verified h.law h.inv },
  Spec.Ecdsa.BrainpoolP256r1.verifyApi.artifact X86_64.target {
    notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication calls `vg_brainpoolp256r1_mul`, a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), which hold for any `a`. \
      Inversions use divsteps, by calls of `vg_brainpoolp256r1_inv_mod_p` and `vg_brainpoolp256r1_inv_mod_n`. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.Ecdsa.Verify.X86_64.verifyBrainpoolP256r1
    stack := 8
    verified := Proof.Ecdsa.Verify.X86_64.BrainpoolP256r1.verify_verified h.law h.inv }]

end VG.Generic.BrainpoolP256r1.X86_64.EcdsaBrainpoolP256r1
