module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P192
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P192Decompress
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.P192.X86_64.Law

/-! # Standalone P192 public-point compression on x86-64 -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP192.X86_64

open VG.Proof.P192.X86_64 (hasLaw)
open VG.Proof.EcKey.Compressed.X86_64.P192

def artifacts : List Artifact :=
  [Spec.EcKey.P192.inst.compressPublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified hasLaw.inv false
    stack := 8 },
    Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact X86_64.target {
      code := Proof.EcKey.Compressed.X86_64.P192Decompress.code false
      verified := Proof.EcKey.Compressed.X86_64.P192Decompress.verified hasLaw.law hasLaw.inv false
      stack := 8 }]

end VG.Artifacts.EcCompressedP192.X86_64
