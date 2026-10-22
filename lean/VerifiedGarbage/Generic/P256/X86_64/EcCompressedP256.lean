module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P256
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P256Decompress
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Standalone P256 public-point compression on x86-64 -/

@[expose] public section

namespace VG.Generic.P256.X86_64.EcCompressedP256

open VG.Proof.EcKey.Compressed.X86_64.P256

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P256.curve) : List Artifact :=
  [false, true].flatMap fun adx =>
    [
    Spec.EcKey.P256.inst.compressPublicKeyApi.artifact X86_64.target {
      suffix := if adx then "_adx" else ""
      code := code adx
      verified := verified h.inv adx
      stack := 8
      features := if adx then ["bmi2", "adx"] else [] },
    Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact X86_64.target {
      suffix := if adx then "_adx" else ""
      code := Proof.EcKey.Compressed.X86_64.P256Decompress.code adx
      verified := Proof.EcKey.Compressed.X86_64.P256Decompress.verified h.law h.inv adx
      stack := 8
      features := if adx then ["bmi2", "adx"] else [] }]

end VG.Generic.P256.X86_64.EcCompressedP256
