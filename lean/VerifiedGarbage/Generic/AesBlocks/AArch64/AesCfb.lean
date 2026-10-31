module

public import VerifiedGarbage.Proof.AesCfb.AArch64.Verified
public import VerifiedGarbage.Proof.AesCfb.AArch64.Caller
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesCfb.AArch64.Body

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on AArch64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.AArch64.AesCfb

open VG.Proof.AesCfb.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesCfb.AArch64.encrypt v.enc
    verified := encrypt_verified v
    features := v.features },
  Spec.Cfb.aesDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Caller.decrypt v
    verified := Caller.verified v
    written := Caller.written v
    writtenOk := Caller.written_ok v
    features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesCfb
