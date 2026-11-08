module

public import VerifiedGarbage.Proof.AesCbc.X86.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-CBC (NIST SP 800-38A §6.2) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCbc.X86

open VG.Proof.AesCbc.X86.Wiped

def artifactsFor (v : Proof.Aes.X86.BlocksImpl) : List Artifact :=
  (if h : v.encWritten = 0 then [
    Spec.Cbc.aesEncryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCbc.X86.encryptZ v.enc
      stack := 24
      verified := encrypt_free v h
      spSafe := encryptZ_spSafe v
      features := v.features }]
  else [
    Spec.Cbc.aesEncryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCbc.X86.Wiped.encrypt v.enc v.suffix v.encWritten
      stack := 72
      verified := encrypt_verified v
      spSafe := encrypt_spSafe v
      features := v.features }]) ++
  (if h : v.decWritten = 0 then [
    Spec.Cbc.aesDecryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCbc.X86.decryptZ v.dec
      stack := 24
      verified := decrypt_free v h
      spSafe := decryptZ_spSafe v
      features := v.features }]
  else [
    Spec.Cbc.aesDecryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCbc.X86.Wiped.decrypt v.dec v.suffix v.decWritten
      stack := 72
      verified := decrypt_verified v
      spSafe := decrypt_spSafe v
      features := v.features }])

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.AesCbc.X86
