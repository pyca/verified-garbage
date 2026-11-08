module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P384
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P384Decompress
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.P384.X86_64.Law

/-! # Standalone P384 public-point compression on x86-64 -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP384.X86_64

open VG.Proof.P384.X86_64 (hasLaw)
open VG.Proof.EcKey.Compressed.X86_64.P384

def artifacts : List Artifact :=
  [false, true].flatMap fun adx =>
    [
    Spec.EcKey.P384.inst.compressPublicKeyApi.artifact X86_64.target {
      suffix := if adx then "_adx" else ""
      code := code adx
      verified := verified hasLaw.inv adx
      stack := 8
      features := if adx then ["bmi2", "adx"] else [] },
    Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact X86_64.target {
      suffix := if adx then "_adx" else ""
      code := Proof.EcKey.Compressed.X86_64.P384Decompress.code adx
      verified := Proof.EcKey.Compressed.X86_64.P384Decompress.verified hasLaw.law hasLaw.inv adx
      stack := 8
      features := if adx then ["bmi2", "adx"] else [] }]

end VG.Artifacts.EcCompressedP384.X86_64
