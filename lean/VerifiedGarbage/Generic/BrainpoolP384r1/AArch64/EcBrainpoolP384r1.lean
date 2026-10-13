module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.EcKey.AArch64.BrainpoolP384r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! # brainpoolP384r1 on AArch64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.AArch64.EcBrainpoolP384r1

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP384r1.curve) : List Artifact := [
  { Spec.EcKey.BrainpoolP384r1.publicKeyApi with
    target := AArch64.target
    doc := Spec.EcKey.BrainpoolP384r1.publicKeyApi.doc (notes := ["Field elements are six 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 384-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), which hold for any `a`. \
      The inversion is a call of `vg_brainpoolp384r1_inv_mod_p`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.EcKey.AArch64.publicKeyBrainpoolP384r1
    contract := Spec.EcKey.BrainpoolP384r1.inst.publicKeyContract AArch64.abi
    verified := Proof.EcKey.AArch64.BrainpoolP384r1.pk_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.BrainpoolP384r1.AArch64.EcBrainpoolP384r1
