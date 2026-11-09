module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.EcKey.AArch64.BrainpoolP384r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.EcKey.AArch64.BrainpoolP384r1.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.BrainpoolP384r1
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.AArch64
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
public import VerifiedGarbage.Proof.BrainpoolP384r1.AArch64.Law
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP384r1
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP384r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface

/-! # brainpoolP384r1 public keys (FIPS 186-5 §A.2) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP384r1.AArch64

open VG.Proof.BrainpoolP384r1.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.publicKeyBrainpoolP384r1
    verified := Proof.EcKey.AArch64.BrainpoolP384r1.pk_verified hasLaw.law hasLaw.inv },
  Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.BrainpoolP384r1.code
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP384r1.verified hasLaw.inv },
  Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.BrainpoolP384r1Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP384r1Decompress.verified hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcBrainpoolP384r1.AArch64
