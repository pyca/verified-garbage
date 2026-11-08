module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP384r1
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP384r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.BrainpoolP384r1.X86.Law

/-! # SEC 1 point conversion with BrainpoolP384r1's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedBrainpoolP384r1.X86

open VG.Proof.BrainpoolP384r1.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.BrainpoolP384r1.code
    verified := Proof.EcKey.Compressed.X86.BrainpoolP384r1.verified },
  Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.BrainpoolP384r1Decompress.code
    verified := Proof.EcKey.Compressed.X86.BrainpoolP384r1Decompress.verified hasLaw.law }]

end VG.Artifacts.EcCompressedBrainpoolP384r1.X86
