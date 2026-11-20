module

public import VerifiedGarbage.Proof.AesSiv.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86

/-! # AES-SIV (RFC 5297) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesSiv.X86

open VG.Proof.AesSiv.X86.Scrub

def artifacts : List Artifact :=
  VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun (v : Proof.Aes.X86.Ctr32Impl) => [
    Spec.Siv.initApi.artifact X86.target (initReg v),
    Spec.Siv.encryptApi.artifact X86.target (encryptReg v),
    Spec.Siv.decryptApi.artifact X86.target (decryptReg v)]

end VG.Artifacts.AesSiv.X86
