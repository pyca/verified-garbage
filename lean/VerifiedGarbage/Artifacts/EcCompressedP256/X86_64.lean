module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P256
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P256Decompress
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.P256.X86_64.Law

/-! # Standalone P256 public-point compression on x86-64 -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP256.X86_64

open VG.Proof.P256.X86_64 (hasLaw)
open VG.Proof.EcKey.Compressed.X86_64.P256

def artifacts : List Artifact :=
  [false, true].flatMap fun adx =>
    [
    Spec.EcKey.P256.inst.compressPublicKeyApi.artifact X86_64.target {
      suffix := if adx then "_adx" else ""
      code := code adx
      verified := verified hasLaw.inv adx
      stack := 8
      features := if adx then ["bmi2", "adx"] else [] },
    Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact X86_64.target {
      suffix := if adx then "_adx" else ""
      code := Proof.EcKey.Compressed.X86_64.P256Decompress.code adx
      verified := Proof.EcKey.Compressed.X86_64.P256Decompress.verified hasLaw.law hasLaw.inv adx
      stack := 8
      features := if adx then ["bmi2", "adx"] else [] }]

end VG.Artifacts.EcCompressedP256.X86_64
