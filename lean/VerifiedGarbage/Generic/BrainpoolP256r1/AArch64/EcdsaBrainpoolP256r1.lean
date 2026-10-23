module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Verified
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Verified
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP256r1
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Verified
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
public import VerifiedGarbage.Proof.Ecdsa.Projective
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Points
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Sum
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Rep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Points
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Sum
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Rep
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad

/-! # brainpoolP256r1 on AArch64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.AArch64.EcdsaBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.Ecdsa.BrainpoolP256r1.signApi.artifact AArch64.target {
    notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a seven-bit fixed-base comb with 37 complete general-curve additions. \
      Each table is scanned in constant time and the signed entry is selected with SIMD masks. \
      Inversions are calls of `vg_brainpoolp256r1_inv_mod_p` and `vg_brainpoolp256r1_inv_mod_n`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."]
    consts := Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg.combConsts
    code := Impl.Ecdsa.AArch64.BrainpoolP256r1.signComb
    verified := Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.sign_verified h.law h.inv },
  Spec.Ecdsa.BrainpoolP256r1.verifyApi.artifact AArch64.target {
    notes := ["Field elements are four 64-bit words in Montgomery form. \
      Public scalar multiplication uses a joint radix-four table built by a shared addition loop, \
      with 256 shared doublings and at most 128 additions using complete general RCB formulas. \
      The inversion modulo `n` is a call of `vg_brainpoolp256r1_inv_mod_n`, by divsteps. \
      Branches and memory addresses depend only on pointers, counters and public verification scalars."]
    code := Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.verify
    verified := Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.verify_verified h.law h.inv }]

end VG.Generic.BrainpoolP256r1.AArch64.EcdsaBrainpoolP256r1
