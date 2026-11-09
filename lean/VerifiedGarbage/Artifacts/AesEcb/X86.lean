module

public import VerifiedGarbage.Proof.AesEcb.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-ECB (NIST SP 800-38A §6.1) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesEcb.X86

open VG.Proof.AesEcb.X86

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) =>
    (encryptRegs v).map (Spec.AesEcb.encryptApi.artifact X86.target) ++
      (decryptRegs v).map (Spec.AesEcb.decryptApi.artifact X86.target)

end VG.Artifacts.AesEcb.X86
