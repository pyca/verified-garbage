module

import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Ecdh.AArch64.BrainpoolP512r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-! # brainpoolP512r1 on AArch64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.AArch64.EcdhBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP512r1.curve) : List Artifact := [
  { Spec.Ecdh.BrainpoolP512r1.exchangeApi with
    target := AArch64.target
    doc := Spec.Ecdh.BrainpoolP512r1.exchangeApi.doc (notes := ["Field elements are eight 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 512-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), which hold for any `a`. \
      The inversion is a call of `vg_brainpoolp512r1_inv_mod_p`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdh.AArch64.BrainpoolP512r1.exchange
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP512r1.inst AArch64.abi
    verified := Proof.Ecdh.AArch64.BrainpoolP512r1.ecdh_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.BrainpoolP512r1.AArch64.EcdhBrainpoolP512r1
