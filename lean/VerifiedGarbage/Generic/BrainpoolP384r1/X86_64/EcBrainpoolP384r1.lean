module

import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.EcKey.X86_64.BrainpoolP384r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration

/-! # brainpoolP384r1 on x86-64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.X86_64.EcBrainpoolP384r1

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.publicKeyApi.artifact X86_64.target {
    notes := ["Field elements are six 64-bit words in Montgomery form. \
      Scalar multiplication calls `vg_brainpoolp384r1_mul`, a fixed 384-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), which hold for any `a`. \
      Inversions use divsteps, by a call of `vg_brainpoolp384r1_inv_mod_p`. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.EcKey.X86_64.publicKeyBrainpoolP384r1
    stack := 8
    verified := Proof.EcKey.X86_64.BrainpoolP384r1.pk_verified h.law h.inv }]

end VG.Generic.BrainpoolP384r1.X86_64.EcBrainpoolP384r1
