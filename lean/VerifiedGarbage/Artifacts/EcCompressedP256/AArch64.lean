module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P256
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P256Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.P256.AArch64.Law

/-! # SEC 1 point conversion with P256's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP256.AArch64

open VG.Proof.P256.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P256.code
    verified := Proof.EcKey.Compressed.AArch64.P256.verified hasLaw.inv },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P256Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.P256Decompress.verified hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcCompressedP256.AArch64
