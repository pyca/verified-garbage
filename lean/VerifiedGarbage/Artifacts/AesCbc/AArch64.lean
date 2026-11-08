module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Lit
public import VerifiedGarbage.Proof.AesCbc.AArch64.Caller
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64

/-! # AES-CBC decryption with seven independent AES states -/

@[expose] public section

namespace VG.Artifacts.AesCbc.AArch64

def direct : List Artifact := [
  Spec.Cbc.aesDecryptApi.artifact VG.AArch64.target {
    suffix := "_aes_sha3"
    code := Impl.AesCbc.AArch64.Decrypt.code
    verified := Proof.AesCbc.AArch64.Wiped.decryptSha3_scrubbed
    features := ["aes","sha3"]
    written := [("scratch",0)]
    writtenOk := Proof.AesCbc.AArch64.Decrypt.written },
  Spec.Cbc.aesDecryptApi.artifact VG.AArch64.target {
    suffix := "_aes"
    code := Impl.AesCbc.AArch64.Decrypt.codeAes
    verified := Proof.AesCbc.AArch64.Wiped.decryptAes_scrubbed
    features := ["aes"]
    written := [("scratch",0)]
    writtenOk := Proof.AesCbc.AArch64.Decrypt.writtenAes }]

end VG.Artifacts.AesCbc.AArch64

-- AES-CBC (NIST SP 800-38A §6.2) on AArch64
namespace VG.Artifacts.AesCbc.AArch64.AesBlocks

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

end VG.Artifacts.AesCbc.AArch64.AesBlocks

namespace VG.Artifacts.AesCbc.AArch64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.AesBlocks.AArch64.variants.flatMap fun v => AesBlocks.artifacts v)

end VG.Artifacts.AesCbc.AArch64
