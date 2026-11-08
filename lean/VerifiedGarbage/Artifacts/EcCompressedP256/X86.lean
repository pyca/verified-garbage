module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P256
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P256Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.P256.X86.Law

/-! # SEC 1 point conversion with P256's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP256.X86

open VG.Proof.P256.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.P256.code
    verified := Proof.EcKey.Compressed.X86.P256.verified hasLaw.inv },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.P256Decompress.code
    verified := Proof.EcKey.Compressed.X86.P256Decompress.verified hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcCompressedP256.X86
