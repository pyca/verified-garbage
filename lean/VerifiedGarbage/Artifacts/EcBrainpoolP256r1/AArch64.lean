module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.EcKey.AArch64.BrainpoolP256r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.EcKey.AArch64.BrainpoolP256r1.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.AArch64
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
public import VerifiedGarbage.Proof.BrainpoolP256r1.AArch64.Law
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP256r1
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP256r1Decompress
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Residue
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface

/-! # brainpoolP256r1 public keys (FIPS 186-5 §A.2) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP256r1.AArch64

open VG.Proof.BrainpoolP256r1.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    code := Impl.EcKey.AArch64.publicKeyBrainpoolP256r1
    verified := Proof.EcKey.AArch64.BrainpoolP256r1.pk_verified hasLaw.law hasLaw.inv }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17],
       [.v29],
       []⟩ (Proof.EcKey.AArch64.Scrub.publicKeyOk _)),
  Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    code := Proof.EcKey.Compressed.AArch64.BrainpoolP256r1.code
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP256r1.verified hasLaw.inv }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17],
       [.v28],
       []⟩ (Proof.EcKey.AArch64.Scrub.compressOk _)),
  Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.Residue.cleared [.x16, .x17] []
      Proof.EcKey.Compressed.AArch64.BrainpoolP256r1Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.Residue.BrainpoolP256r1.verified hasLaw.law hasLaw.inv
    residue := some ⟨Proof.EcKey.Compressed.AArch64.Residue.BrainpoolP256r1.noResidue hasLaw.law hasLaw.inv⟩ }]

end VG.Artifacts.EcBrainpoolP256r1.AArch64
