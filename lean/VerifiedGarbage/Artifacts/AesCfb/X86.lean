module

public import VerifiedGarbage.Proof.AesCfb.X86.Verified
public import VerifiedGarbage.Proof.AesCfb.X86.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCfb.X86

open VG.Proof.AesCfb.X86

def artifactsFor (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesCfb.X86.encrypt v.enc
    stack := 24
    verified := Proof.AesCfb.encrypt_keyed (encrypt_verified v)
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.Cfb.aesDecryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesCfb.X86.decrypt v.enc
    stack := 24
    verified := Proof.AesCfb.decrypt_keyed (decrypt_verified v)
    spSafe := decrypt_spSafe v
    features := v.features },
  Spec.Cfb.aesEncryptFinalApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratchWiped 48 6 4 (Impl.AesCfb.X86.encryptFinal v.enc v.suffix)
    stack := 100
    verified := Proof.AesCfb.encryptFinal_keyed (encryptFinal_framed v)
    spSafe := encryptFinal_framed_spSafe v
    features := v.features },
  Spec.Cfb.aesDecryptFinalApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratchWiped 48 6 4 (Impl.AesCfb.X86.decryptFinal v.enc v.suffix)
    stack := 100
    verified := Proof.AesCfb.decryptFinal_keyed (decryptFinal_framed v)
    spSafe := decryptFinal_framed_spSafe v
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.AesCfb.X86
