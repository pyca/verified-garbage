module

public import VerifiedGarbage.Proof.AesCfb8.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86_64

/-! # AES-CFB8 (NIST SP 800-38A §6.3, with 8-bit segments) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesCfb8.X86_64

open VG.Proof.AesCfb8.X86_64

def artifactsFor (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact := [
  Spec.Cfb8.aesEncryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesCfb8.X86_64.encrypt v.enc
    stack := 8
    verified := Proof.AesCfb8.encrypt_keyed (encrypt_verified v)
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.Cfb8.aesDecryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesCfb8.X86_64.decrypt v.enc
    stack := 8
    verified := Proof.AesCfb8.decrypt_keyed (decrypt_verified v)
    spSafe := decrypt_spSafe v
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.AesCfb8.X86_64
