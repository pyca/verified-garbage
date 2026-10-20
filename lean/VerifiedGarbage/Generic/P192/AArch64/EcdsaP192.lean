module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Verified
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
public import VerifiedGarbage.Proof.Ecdsa.Projective
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Points
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Sum
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Rep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Points
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Sum
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Rep
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad

/-! # p192 on AArch64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.P192.AArch64.EcdsaP192

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P192.curve) : List Artifact := [
  Spec.Ecdsa.P192.signApi.artifact AArch64.target {
    notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1). \
      Inversions are calls of `vg_p192_inv_mod_p` and `vg_p192_inv_mod_n`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.Ecdsa.AArch64.signP192
    verified := Proof.Ecdsa.AArch64.P192.sign_verified h.law h.inv },
  Spec.Ecdsa.P192.verifyApi.artifact AArch64.target {
    notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1). \
      Inversions are calls of `vg_p192_inv_mod_p` and `vg_p192_inv_mod_n`, by divsteps. \
      Branches and memory addresses depend only on pointers and loop counters."]
    code := Impl.Ecdsa.Verify.AArch64.P192.verify
    verified := Proof.Ecdsa.Verify.AArch64.P192.verify_verified h.law h.inv }]

end VG.Generic.P192.AArch64.EcdsaP192
