module

import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.EcKey.AArch64.P192.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! # p192 on AArch64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.P192.AArch64.EcP192

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P192.curve) : List Artifact := [
  { Spec.EcKey.P192.publicKeyApi with
    target := AArch64.target
    doc := Spec.EcKey.P192.publicKeyApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1). \
      The inversion is a call of `vg_p192_inv_mod_p`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.EcKey.AArch64.publicKeyP192
    contract := Spec.EcKey.P192.inst.publicKeyContract AArch64.abi
    verified := Proof.EcKey.AArch64.P192.pk_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P192.AArch64.EcP192
