module

public import VerifiedGarbage.Proof.AesCbc.X86.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-CBC (NIST SP 800-38A §6.2) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCbc.X86

open VG.Proof.AesCbc.X86.Wiped

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) =>
    (encryptRegs v).map (Spec.Cbc.aesEncryptApi.artifact X86.target) ++
      (decryptRegs v).map (Spec.Cbc.aesDecryptApi.artifact X86.target)

end VG.Artifacts.AesCbc.X86
