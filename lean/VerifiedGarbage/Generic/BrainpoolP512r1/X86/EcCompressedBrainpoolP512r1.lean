module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP512r1
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP512r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with BrainpoolP512r1's existing field backend -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.X86.EcCompressedBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.BrainpoolP512r1.code
    verified := Proof.EcKey.Compressed.X86.BrainpoolP512r1.verified },
  Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.BrainpoolP512r1Decompress.code
    verified := Proof.EcKey.Compressed.X86.BrainpoolP512r1Decompress.verified h.law }]

end VG.Generic.BrainpoolP512r1.X86.EcCompressedBrainpoolP512r1
