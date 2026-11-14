module

public import VerifiedGarbage.Proof.AesEcb.AArch64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64

/-! # AES-ECB (NIST SP 800-38A §6.1) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesEcb.AArch64

open VG.Proof.AesEcb.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.BlocksImpl) =>
    (encryptRegs v).map (Spec.AesEcb.encryptApi.artifact AArch64.target) ++
      (decryptRegs v).map (Spec.AesEcb.decryptApi.artifact AArch64.target)

end VG.Artifacts.AesEcb.AArch64
