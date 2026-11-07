module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Caller
public import VerifiedGarbage.Proof.AesCbc.AArch64.Scrubbed
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # AES-CBC (NIST SP 800-38A §6.2) on AArch64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.AArch64.AesCbc

open VG.Proof.AesCbc.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Caller.encrypt v
    verified := Proof.AesCbc.encrypt_keyed (Caller.verified v)
    written := Caller.written v
    writtenOk := Caller.written_ok v
    features := v.features },
  Spec.Cbc.aesDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesCbc.AArch64.decrypt v.dec
    verified := Proof.AesCbc.decrypt_keyed (decrypt_verified v)
    features := v.features },
  Spec.Cbc.aesDecryptScrubbedApi.artifact AArch64.target {
    suffix := v.suffix
    code := Scrubbed.decrypt v
    stack := 32
    verified := Scrubbed.decrypt_verified v
    features := v.features }] ++
  if h : v.enc.name = "vg_aes_encrypt_blocks_aes" then [
    Spec.Cbc.aesEncryptScrubbedApi.artifact AArch64.target {
      suffix := v.suffix
      code := Caller.encrypt v
      verified := Scrubbed.encrypt_free v h
      features := v.features }]
  else [
    Spec.Cbc.aesEncryptScrubbedApi.artifact AArch64.target {
      suffix := v.suffix
      code := Scrubbed.encrypt v
      stack := 32
      verified := Scrubbed.encrypt_verified v
      features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesCbc
