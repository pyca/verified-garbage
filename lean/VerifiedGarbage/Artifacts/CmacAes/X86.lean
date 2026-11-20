module

public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86

/-! # AES-CMAC (NIST SP 800-38B) on x86 -/

@[expose] public section

namespace VG.Artifacts.CmacAes.X86

def artifacts : List Artifact :=
  VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun (v : Proof.Aes.X86.Ctr32Impl) => [
    Spec.Cmac.aesInitApi.artifact X86.target (Proof.CmacAes.Stream.X86.Scrub.initReg v),
    Spec.Cmac.aesAbsorbApi.artifact X86.target (Proof.CmacAes.Stream.X86.Scrub.absorbReg v),
    Spec.Cmac.aesFinishApi.artifact X86.target (Proof.CmacAes.Stream.X86.Scrub.finishReg v)]

end VG.Artifacts.CmacAes.X86
