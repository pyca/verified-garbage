module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! # p192 on AArch64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.P192.AArch64.EcdsaP192

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P192.curve) : List Artifact := [
  { Spec.Ecdsa.P192.signApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P192.signApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1). \
      Inversions are calls of `vg_p192_inv_mod_p` and `vg_p192_inv_mod_n`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdsa.AArch64.signP192
    contract := Spec.Ecdsa.P192.inst.signContract AArch64.abi
    verified := Proof.Ecdsa.AArch64.P192.sign_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ecdsa.P192.verifyApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P192.verifyApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1). \
      Inversions are calls of `vg_p192_inv_mod_p` and `vg_p192_inv_mod_n`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdsa.Verify.AArch64.P192.verify
    contract := Spec.Ecdsa.P192.inst.verifyContract AArch64.abi
    verified := Proof.Ecdsa.Verify.AArch64.P192.verify_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P192.AArch64.EcdsaP192
