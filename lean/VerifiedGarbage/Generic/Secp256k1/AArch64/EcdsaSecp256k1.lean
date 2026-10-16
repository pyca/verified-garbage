module

import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.Framework.Registration

/-! # secp256k1 on AArch64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.Secp256k1.AArch64.EcdsaSecp256k1

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  Spec.Ecdsa.Secp256k1.signApi.artifact AArch64.target {
    notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), including for a = 0. \
      Inversions are calls of `vg_secp256k1_inv_mod_p` and `vg_secp256k1_inv_mod_n`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.Ecdsa.AArch64.signSecp256k1
    verified := Proof.Ecdsa.AArch64.Secp256k1.sign_verified h.law h.inv },
  Spec.Ecdsa.Secp256k1.verifyApi.artifact AArch64.target {
    notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), including for a = 0. \
      The inversion modulo `n` is a call of `vg_secp256k1_inv_mod_n`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.Ecdsa.Verify.AArch64.Secp256k1.verify
    verified := Proof.Ecdsa.Verify.AArch64.Secp256k1.verify_verified h.law h.inv }]

end VG.Generic.Secp256k1.AArch64.EcdsaSecp256k1
