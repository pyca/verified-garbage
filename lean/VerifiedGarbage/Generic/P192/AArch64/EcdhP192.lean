module

import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Ecdh.AArch64.P192.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Framework.Registration

/-! # p192 on AArch64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.P192.AArch64.EcdhP192

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P192.curve) : List Artifact := [
  Spec.Ecdh.P192.exchangeApi.artifact AArch64.target {
    notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1). \
      The inversion is a call of `vg_p192_inv_mod_p`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.Ecdh.AArch64.P192.exchange
    verified := Proof.Ecdh.AArch64.P192.ecdh_verified h.law h.inv }]

end VG.Generic.P192.AArch64.EcdhP192
