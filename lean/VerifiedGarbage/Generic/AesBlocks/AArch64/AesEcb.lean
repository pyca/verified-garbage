module

public import VerifiedGarbage.Proof.AesEcb.AArch64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # AES-ECB (NIST SP 800-38A §6.1) on AArch64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.AArch64.AesEcb

open VG.Proof.AesEcb.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact :=
  if h : v.free = true then [
    Spec.AesEcb.encryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := v.enc.code
      verified := encrypt_free v h
      features := v.features },
    Spec.AesEcb.decryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := v.dec.code
      verified := decrypt_free v h
      features := v.features }]
  else [
    Spec.AesEcb.encryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := encrypt v
      stack := 32
      verified := encrypt_verified v
      features := v.features },
    Spec.AesEcb.decryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := decrypt v
      stack := 32
      verified := decrypt_verified v
      features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesEcb
