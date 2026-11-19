module

public import VerifiedGarbage.Proof.AesOfb.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-OFB (NIST SP 800-38A §6.4) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesOfb.X86

open VG.Proof.AesOfb.X86.Scrub

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.Ofb.aesApi.artifact X86.target (ofbReg v),
    Spec.Ofb.aesFinalApi.artifact X86.target (ofbFinalReg v)]

end VG.Artifacts.AesOfb.X86
