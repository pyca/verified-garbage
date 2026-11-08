module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P384
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P384Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.P384.X86.Law

/-! # SEC 1 point conversion with P384's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP384.X86

open VG.Proof.P384.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.P384.code
    verified := Proof.EcKey.Compressed.X86.P384.verified },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.P384Decompress.code
    verified := Proof.EcKey.Compressed.X86.P384Decompress.verified hasLaw.law }]

end VG.Artifacts.EcCompressedP384.X86
