module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP512r1
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Lit
public import VerifiedGarbage.Proof.Framework.Contract

/-! # brainpoolP512r1 on AArch64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.AArch64.EcdsaBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.Ecdsa.BrainpoolP512r1.signApi.artifact AArch64.target {
    notes := ["Field elements are eight 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 512-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), which hold for any `a`. \
      Inversions are calls of `vg_brainpoolp512r1_inv_mod_p` and `vg_brainpoolp512r1_inv_mod_n`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.Ecdsa.AArch64.signBrainpoolP512r1
    verified := Proof.Ecdsa.AArch64.BrainpoolP512r1.sign_verified h.law h.inv },
  Spec.Ecdsa.BrainpoolP512r1.verifyApi.artifact AArch64.target {
    notes := ["Field elements are eight 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 512-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), which hold for any `a`. \
      The inversion modulo `n` is a call of `vg_brainpoolp512r1_inv_mod_n`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.verify
    verified := Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.verify_verified h.law h.inv }]

end VG.Generic.BrainpoolP512r1.AArch64.EcdsaBrainpoolP512r1
