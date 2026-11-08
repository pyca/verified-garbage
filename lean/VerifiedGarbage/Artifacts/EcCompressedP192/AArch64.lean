module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P192
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P192Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.P192.AArch64.Law

/-! # SEC 1 point conversion with P192's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP192.AArch64

open VG.Proof.P192.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P192.code
    verified := Proof.EcKey.Compressed.AArch64.P192.verified hasLaw.inv },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P192Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.P192Decompress.verified hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcCompressedP192.AArch64
