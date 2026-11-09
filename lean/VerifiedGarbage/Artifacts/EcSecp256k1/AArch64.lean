module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.EcKey.AArch64.Secp256k1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.EcKey.AArch64.Secp256k1.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.Secp256k1
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.AArch64
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Secp256k1.AArch64.Law

/-! # secp256k1 on AArch64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Artifacts.EcSecp256k1.AArch64

open VG.Proof.Secp256k1.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.Secp256k1.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.publicKeySecp256k1
    verified := Proof.EcKey.AArch64.Secp256k1.pk_verified hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcSecp256k1.AArch64
