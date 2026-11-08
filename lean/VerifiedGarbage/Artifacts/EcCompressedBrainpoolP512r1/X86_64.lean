module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.BrainpoolP512r1
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.BrainpoolP512r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.BrainpoolP512r1.X86_64.Law

/-! # Standalone BrainpoolP512r1 public-point compression on x86-64 -/

@[expose] public section

namespace VG.Artifacts.EcCompressedBrainpoolP512r1.X86_64

open VG.Proof.BrainpoolP512r1.X86_64 (hasLaw)
open VG.Proof.EcKey.Compressed.X86_64.BrainpoolP512r1

def artifacts : List Artifact :=
  [Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified hasLaw.inv false
    stack := 8 },
    Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact X86_64.target {
      code := Proof.EcKey.Compressed.X86_64.BrainpoolP512r1Decompress.code false
      verified := Proof.EcKey.Compressed.X86_64.BrainpoolP512r1Decompress.verified hasLaw.law hasLaw.inv false
      stack := 8 }]

end VG.Artifacts.EcCompressedBrainpoolP512r1.X86_64
