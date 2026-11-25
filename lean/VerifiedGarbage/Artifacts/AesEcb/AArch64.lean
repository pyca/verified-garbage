module

public import VerifiedGarbage.Proof.AesEcb.AArch64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64

/-! # AES-ECB (NIST SP 800-38A §6.1) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesEcb.AArch64

open VG.Proof.AesEcb.AArch64

def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.AesBlocks.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.BlocksImpl) => [
    Spec.AesEcb.encryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesEcb.AArch64.Fn.blocks v.enc
      verified := Proof.AesEcb.AArch64.encrypt_scrubbed v
      publicOutOk := Proof.AesEcb.AArch64.encrypt_public v },
    Spec.AesEcb.decryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesEcb.AArch64.Fn.blocks v.dec
      verified := Proof.AesEcb.AArch64.decrypt_scrubbed v
      publicOutOk := Proof.AesEcb.AArch64.decrypt_public v }]

end VG.Artifacts.AesEcb.AArch64
