module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P192
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P192Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.P192.X86.Law

/-! # SEC 1 point conversion with P192's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP192.X86

open VG.Proof.P192.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.P192.code
    verified := Proof.EcKey.Compressed.X86.P192.verified },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.P192Decompress.code
    verified := Proof.EcKey.Compressed.X86.P192Decompress.verified hasLaw.law }]

end VG.Artifacts.EcCompressedP192.X86
