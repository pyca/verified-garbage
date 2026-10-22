module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP256r1
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP256r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with BrainpoolP256r1's existing field backend -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.Arm.EcCompressedBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.BrainpoolP256r1.code
    verified := Proof.EcKey.Compressed.Arm.BrainpoolP256r1.verified },
  Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.BrainpoolP256r1Decompress.code
    verified := Proof.EcKey.Compressed.Arm.BrainpoolP256r1Decompress.verified h.law }]

end VG.Generic.BrainpoolP256r1.Arm.EcCompressedBrainpoolP256r1
