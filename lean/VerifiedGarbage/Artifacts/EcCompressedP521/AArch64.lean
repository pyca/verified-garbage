module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P521
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P521Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.P521.AArch64.Law

/-! # SEC 1 point conversion with P521's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP521.AArch64

open VG.Proof.P521.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P521.code
    verified := Proof.EcKey.Compressed.AArch64.P521.verified hasLaw.inv },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P521Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.P521Decompress.verified hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcCompressedP521.AArch64
