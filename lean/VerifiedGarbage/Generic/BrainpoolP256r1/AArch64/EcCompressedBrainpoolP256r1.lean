module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP256r1
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP256r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with BrainpoolP256r1's existing field backend -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.AArch64.EcCompressedBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.BrainpoolP256r1.code
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP256r1.verified h.inv },
  Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.BrainpoolP256r1Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP256r1Decompress.verified h.law h.inv }]

end VG.Generic.BrainpoolP256r1.AArch64.EcCompressedBrainpoolP256r1
