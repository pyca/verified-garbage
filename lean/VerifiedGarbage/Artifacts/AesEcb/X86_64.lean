module

public import VerifiedGarbage.Proof.AesEcb.X86_64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86_64
public import VerifiedGarbage.Proof.Variants.Zeroize.X86_64

/-! # AES-ECB (NIST SP 800-38A §6.1) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesEcb.X86_64

open VG.Proof.AesEcb.X86_64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86_64.variants.flatMap fun (v : Proof.Aes.X86_64.BlocksImpl) =>
    VG.Proof.Variants.Zeroize.X86_64.variants.flatMap fun (z : Proof.Zeroize.X86_64.ZeroizeImpl) =>
    (encryptRegs v z).map (Spec.AesEcb.encryptApi.artifact X86_64.target) ++
      (decryptRegs v z).map (Spec.AesEcb.decryptApi.artifact X86_64.target)

end VG.Artifacts.AesEcb.X86_64
