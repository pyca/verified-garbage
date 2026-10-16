module

import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! # brainpoolP512r1 on AArch64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.AArch64.EcdsaBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP512r1.curve) : List Artifact := [
  { Spec.Ecdsa.BrainpoolP512r1.signApi with
    target := AArch64.target
    doc := Spec.Ecdsa.BrainpoolP512r1.signApi.doc (notes := ["Field elements are eight 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 512-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), which hold for any `a`. \
      Inversions are calls of `vg_brainpoolp512r1_inv_mod_p` and `vg_brainpoolp512r1_inv_mod_n`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdsa.AArch64.signBrainpoolP512r1
    contract := Spec.Ecdsa.BrainpoolP512r1.inst.signContract AArch64.abi
    verified := Proof.Ecdsa.AArch64.BrainpoolP512r1.sign_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ecdsa.BrainpoolP512r1.verifyApi with
    target := AArch64.target
    doc := Spec.Ecdsa.BrainpoolP512r1.verifyApi.doc (notes := ["Field elements are eight 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 512-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), which hold for any `a`. \
      The inversion modulo `n` is a call of `vg_brainpoolp512r1_inv_mod_n`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.verify
    contract := Spec.Ecdsa.BrainpoolP512r1.inst.verifyContract AArch64.abi
    verified := Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.verify_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.BrainpoolP512r1.AArch64.EcdsaBrainpoolP512r1
