module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP512r1
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP512r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with BrainpoolP512r1's existing field backend -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.AArch64.EcCompressedBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.BrainpoolP512r1.code
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP512r1.verified h.inv },
  Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.BrainpoolP512r1Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP512r1Decompress.verified h.law h.inv }]

end VG.Generic.BrainpoolP512r1.AArch64.EcCompressedBrainpoolP512r1
