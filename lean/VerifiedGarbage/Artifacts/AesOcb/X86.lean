module

public import VerifiedGarbage.Proof.AesOcb.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-OCB (RFC 7253) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesOcb.X86

open VG.Proof.AesOcb.X86.Scrub

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.Ocb.initApi.artifact X86.target (initReg v),
    Spec.Ocb.sealApi.artifact X86.target (sealReg v),
    Spec.Ocb.openApi.artifact X86.target (openReg v)]

end VG.Artifacts.AesOcb.X86
