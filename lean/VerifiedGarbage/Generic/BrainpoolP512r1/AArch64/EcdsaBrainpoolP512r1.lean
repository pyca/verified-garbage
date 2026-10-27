module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Verified
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.AArch64.Joint

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
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Verified
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
public import VerifiedGarbage.Proof.Ecdsa.Projective
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Points
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Sum
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Rep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Points
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Sum
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Rep
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad

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
      Joint radix-four multiplication shares 512 doublings and uses a fifteen-entry public table built by a shared addition loop. \
      General complete addition formulas of Renes, Costello and Batina (Algorithm 1) handle any `a`. \
      The inversion modulo `n` is a call of `vg_brainpoolp512r1_inv_mod_n`, by divsteps. \
      Lookup addresses and zero-digit branches depend on the public digest and signature; \
      other branches and addresses depend only on pointers and loop counters."]
    code := Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.verify
    verified := Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.verify_verified h.law h.inv }]

end VG.Generic.BrainpoolP512r1.AArch64.EcdsaBrainpoolP512r1
