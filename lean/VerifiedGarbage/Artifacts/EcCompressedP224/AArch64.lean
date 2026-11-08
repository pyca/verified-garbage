module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P224
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P224Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.P224.AArch64.Law

/-! # SEC 1 point conversion with P224's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP224.AArch64

open VG.Proof.P224.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P224.code
    verified := Proof.EcKey.Compressed.AArch64.P224.verified hasLaw.inv },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P224Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.P224Decompress.verified hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcCompressedP224.AArch64
