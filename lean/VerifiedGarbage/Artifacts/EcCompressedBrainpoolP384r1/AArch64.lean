module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP384r1
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP384r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.BrainpoolP384r1.AArch64.Law

/-! # SEC 1 point conversion with BrainpoolP384r1's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedBrainpoolP384r1.AArch64

open VG.Proof.BrainpoolP384r1.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.BrainpoolP384r1.code
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP384r1.verified hasLaw.inv },
  Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.BrainpoolP384r1Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP384r1Decompress.verified hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcCompressedBrainpoolP384r1.AArch64
