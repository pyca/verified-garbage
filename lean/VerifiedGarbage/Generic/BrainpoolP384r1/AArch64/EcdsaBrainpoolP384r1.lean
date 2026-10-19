module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Lit
public import VerifiedGarbage.Proof.Framework.Contract

/-! # brainpoolP384r1 on AArch64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.AArch64.EcdsaBrainpoolP384r1

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdsa.BrainpoolP384r1.signApi.artifact AArch64.target {
    notes := ["Field elements are six 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 384-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), which hold for any `a`. \
      Inversions are calls of `vg_brainpoolp384r1_inv_mod_p` and `vg_brainpoolp384r1_inv_mod_n`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.Ecdsa.AArch64.signBrainpoolP384r1
    verified := Proof.Ecdsa.AArch64.BrainpoolP384r1.sign_verified h.law h.inv },
  Spec.Ecdsa.BrainpoolP384r1.verifyApi.artifact AArch64.target {
    notes := ["Field elements are six 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 384-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), which hold for any `a`. \
      The inversion modulo `n` is a call of `vg_brainpoolp384r1_inv_mod_n`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.verify
    verified := Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.verify_verified h.law h.inv }]

end VG.Generic.BrainpoolP384r1.AArch64.EcdsaBrainpoolP384r1
