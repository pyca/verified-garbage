module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Caller
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CBC (NIST SP 800-38A §6.2) on AArch64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.AArch64.AesCbc

open VG.Proof.AesCbc.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Caller.encrypt v
    verified := Caller.verified v
    written := Caller.written v
    writtenOk := Caller.written_ok v
    features := v.features },
  Spec.Cbc.aesDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesCbc.AArch64.decrypt v.dec
    verified := decrypt_verified v
    features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesCbc
