module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P384.Comb7
public import VerifiedGarbage.Impl.EcKey.P384.AArch64
import VerifiedGarbage.Proof.EcKey.AArch64.P384.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.EcKey.AArch64.P384.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.P384
public import VerifiedGarbage.Proof.EcKey.AArch64.P384.Verified
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Ecdh.P384.AArch64
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.P384.Point
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Impl.Ecdh.P384.AArch64
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Proof.Weierstrass.MulContract

/-! # P-384 public keys (FIPS 186-5 §A.2) on AArch64 -/

@[expose] public section

namespace VG.Generic.P384.AArch64.EcP384

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P384.curve) : List Artifact := [
  Spec.EcKey.P384.publicKeyApi.artifact AArch64.target {
    consts := Impl.Ecdsa.AArch64.p384.combConsts
    code := Impl.EcKey.AArch64.publicKeyP384
    verified := Proof.EcKey.AArch64.P384.pk_verified h.law h.inv (Proof.P384.combOk7 h.law) }]

end VG.Generic.P384.AArch64.EcP384
