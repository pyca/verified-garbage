module

import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.EcKey.X86_64.Secp256k1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration

/-! # secp256k1 on x86-64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.Secp256k1.X86_64.EcSecp256k1

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  Spec.EcKey.Secp256k1.publicKeyApi.artifact X86_64.target {
    notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication calls `vg_secp256k1_mul`, a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), including for a = 0. \
      Inversions use divsteps, by a call of `vg_secp256k1_inv_mod_p`. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.EcKey.X86_64.publicKeySecp256k1
    stack := 8
    verified := Proof.EcKey.X86_64.Secp256k1.pk_verified h.law h.inv }]

end VG.Generic.Secp256k1.X86_64.EcSecp256k1
