module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.BrainpoolP384r1
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.BrainpoolP384r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.BrainpoolP384r1.X86_64.Law

/-! # Standalone BrainpoolP384r1 public-point compression on x86-64 -/

@[expose] public section

namespace VG.Artifacts.EcCompressedBrainpoolP384r1.X86_64

open VG.Proof.BrainpoolP384r1.X86_64 (hasLaw)
open VG.Proof.EcKey.Compressed.X86_64.BrainpoolP384r1

def artifacts : List Artifact :=
  [Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified hasLaw.inv false
    stack := 8 },
    Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact X86_64.target {
      code := Proof.EcKey.Compressed.X86_64.BrainpoolP384r1Decompress.code false
      verified := Proof.EcKey.Compressed.X86_64.BrainpoolP384r1Decompress.verified hasLaw.law hasLaw.inv false
      stack := 8 }]

end VG.Artifacts.EcCompressedBrainpoolP384r1.X86_64
