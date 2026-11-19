module

public import VerifiedGarbage.Proof.AesCcm.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86

/-! # AES-CCM (NIST SP 800-38C) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCcm.X86

open VG.Proof.AesCcm.X86.Scrub

def artifacts : List Artifact :=
  VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun (v : Proof.Aes.X86.Ctr32Impl) => [
    Spec.Ccm.sealApi.artifact X86.target (sealReg v),
    Spec.Ccm.openApi.artifact X86.target (openReg v)]

end VG.Artifacts.AesCcm.X86
