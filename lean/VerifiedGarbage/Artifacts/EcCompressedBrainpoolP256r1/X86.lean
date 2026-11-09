module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP256r1
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP256r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.BrainpoolP256r1.X86.Law

/-! # SEC 1 point conversion with BrainpoolP256r1's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedBrainpoolP256r1.X86

open VG.Proof.BrainpoolP256r1.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.BrainpoolP256r1.code
    verified := Proof.EcKey.Compressed.X86.BrainpoolP256r1.verified hasLaw.inv },
  Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.BrainpoolP256r1Decompress.code
    verified := Proof.EcKey.Compressed.X86.BrainpoolP256r1Decompress.verified hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcCompressedBrainpoolP256r1.X86
