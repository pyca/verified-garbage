module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP512r1
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP512r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.BrainpoolP512r1.X86.Law

/-! # SEC 1 point conversion with BrainpoolP512r1's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedBrainpoolP512r1.X86

open VG.Proof.BrainpoolP512r1.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.BrainpoolP512r1.code
    verified := Proof.EcKey.Compressed.X86.BrainpoolP512r1.verified },
  Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.BrainpoolP512r1Decompress.code
    verified := Proof.EcKey.Compressed.X86.BrainpoolP512r1Decompress.verified hasLaw.law }]

end VG.Artifacts.EcCompressedBrainpoolP512r1.X86
