module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP384r1
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP384r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with BrainpoolP384r1's existing field backend -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.AArch64.EcCompressedBrainpoolP384r1

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.BrainpoolP384r1.code
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP384r1.verified h.inv },
  Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.BrainpoolP384r1Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP384r1Decompress.verified h.law h.inv }]

end VG.Generic.BrainpoolP384r1.AArch64.EcCompressedBrainpoolP384r1
