module

public import VerifiedGarbage.Proof.AesCtr.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86

/-! # AES-CTR (NIST SP 800-38A §6.5) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCtr.X86

open VG.Proof.AesCtr.X86.Scrub

def artifacts : List Artifact :=
  (VG.Proof.Variants.AesCtr32.X86.variants.map fun (v : Proof.Aes.X86.Ctr32Impl) =>
    Spec.Ctr.aesApi.artifact X86.target (ctrReg v)) ++
  VG.Proof.Variants.AesBlocks.X86.variants.map fun (v : Proof.Aes.X86.BlocksImpl) =>
    Spec.Ctr.aesFinalApi.artifact X86.target (ctrFinalReg v)

end VG.Artifacts.AesCtr.X86
