module

public import VerifiedGarbage.Proof.AesOfb.AArch64.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64

/-! # AES-OFB (NIST SP 800-38A §6.4) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesOfb.AArch64

open VG.Proof.AesOfb.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.BlocksImpl) => [
    Spec.Ofb.aesApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesOfb.AArch64.Fn.crypt v.enc
      verified := .scrubbed (crypt_scrubbed v) },
    Spec.Ofb.aesFinalApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesOfb.AArch64.Fn.cryptFinal v.enc v.suffix
      verified := .scrubbed (cryptFinal_scrubbed v) }]

end VG.Artifacts.AesOfb.AArch64
