module

import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1

/-! # secp256k1 on x86-64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.Secp256k1.X86_64.EcdsaSecp256k1

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  Spec.Ecdsa.Secp256k1.signApi.artifact X86_64.target {
    notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication calls `vg_secp256k1_mul`, a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), including for a = 0. \
      Inversions use divsteps, by calls of `vg_secp256k1_inv_mod_p` and `vg_secp256k1_inv_mod_n`. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.Ecdsa.X86_64.signSecp256k1
    stack := 8
    verified := Proof.Ecdsa.X86_64.Secp256k1.sign_verified h.law h.inv },
  Spec.Ecdsa.Secp256k1.verifyApi.artifact X86_64.target {
    notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication calls `vg_secp256k1_mul`, a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), including for a = 0. \
      Inversions use divsteps, by calls of `vg_secp256k1_inv_mod_p` and `vg_secp256k1_inv_mod_n`. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.Ecdsa.Verify.X86_64.verifySecp256k1
    stack := 8
    verified := Proof.Ecdsa.Verify.X86_64.Secp256k1.verify_verified h.law h.inv }]

end VG.Generic.Secp256k1.X86_64.EcdsaSecp256k1
