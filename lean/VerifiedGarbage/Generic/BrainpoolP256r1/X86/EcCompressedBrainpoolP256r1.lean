module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP256r1
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP256r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with BrainpoolP256r1's existing field backend -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.X86.EcCompressedBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.X86.Inv.HasLawInv Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.BrainpoolP256r1.code
    verified := Proof.EcKey.Compressed.X86.BrainpoolP256r1.verified h.inv },
  Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.BrainpoolP256r1Decompress.code
    verified := Proof.EcKey.Compressed.X86.BrainpoolP256r1Decompress.verified h.law h.inv }]

end VG.Generic.BrainpoolP256r1.X86.EcCompressedBrainpoolP256r1
