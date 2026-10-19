module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.EcKey.AArch64.Secp256k1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.EcKey.AArch64.Secp256k1.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.Secp256k1

/-! # secp256k1 on AArch64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.Secp256k1.AArch64.EcSecp256k1

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  Spec.EcKey.Secp256k1.publicKeyApi.artifact AArch64.target {
    notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), including for a = 0. \
      The inversion is a call of `vg_secp256k1_inv_mod_p`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.EcKey.AArch64.publicKeySecp256k1
    verified := Proof.EcKey.AArch64.Secp256k1.pk_verified h.law h.inv }]

end VG.Generic.Secp256k1.AArch64.EcSecp256k1
