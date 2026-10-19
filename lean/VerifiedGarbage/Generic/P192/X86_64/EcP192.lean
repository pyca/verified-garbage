module

import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.EcKey.X86_64.P192.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration

/-! # p192 on x86-64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.P192.X86_64.EcP192

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P192.curve) : List Artifact := [
  Spec.EcKey.P192.publicKeyApi.artifact X86_64.target {
    notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication calls `vg_p192_mul`, a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1). \
      Inversions use divsteps, by a call of `vg_p192_inv_mod_p`. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.EcKey.X86_64.publicKeyP192
    stack := 8
    verified := Proof.EcKey.X86_64.P192.pk_verified h.law h.inv }]

end VG.Generic.P192.X86_64.EcP192
