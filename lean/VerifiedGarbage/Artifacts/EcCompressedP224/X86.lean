module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P224
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P224Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.P224.X86.Law

/-! # SEC 1 point conversion with P224's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP224.X86

open VG.Proof.P224.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.P224.code
    verified := Proof.EcKey.Compressed.X86.P224.verified },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.P224Decompress.code
    verified := Proof.EcKey.Compressed.X86.P224Decompress.verified hasLaw.law }]

end VG.Artifacts.EcCompressedP224.X86
