module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Caller
public import VerifiedGarbage.Proof.AesCbc.AArch64.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # AES-CBC (NIST SP 800-38A §6.2) on AArch64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.AArch64.AesCbc

open VG.Proof.AesCbc.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact :=
  (if h : v.enc.name = "vg_aes_encrypt_blocks_aes" then [
    Spec.Cbc.aesEncryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Caller.encrypt v
      verified := Wiped.encrypt_free_scrubbed v h
      written := Caller.written v
      writtenOk := Caller.written_ok v
      features := v.features }]
  else [
    Spec.Cbc.aesEncryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Wiped.encrypt v
      stack := 32
      verified := Wiped.encrypt_verified v
      features := v.features }]) ++
  -- With the Cryptographic Extension, decryption is `Decrypt.codeAes`
  -- (`Artifacts/AesCbc/AArch64.lean`), which writes no `scratch`.
  if v.free then [] else [
  Spec.Cbc.aesDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Wiped.decrypt v
    stack := 32
    verified := Wiped.decrypt_verified v
    features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesCbc
