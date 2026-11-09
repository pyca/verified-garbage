module

public import VerifiedGarbage.Proof.AesEcb.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-ECB (NIST SP 800-38A §6.1) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesEcb.X86

open VG.Proof.AesEcb.X86

def artifactsFor (v : Proof.Aes.X86.BlocksImpl) : List Artifact :=
  (if h : v.encWritten = 0 then [
    Spec.AesEcb.encryptApi.artifact X86.target {
      suffix := v.suffix
      code := v.enc.code
      verified := encrypt_free v h
      spSafe := v.encSpSafe
      features := v.features }]
  else [
    Spec.AesEcb.encryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesEcb.X86.wiped v.enc v.encWritten
      stack := 32
      verified := encrypt_verified v
      spSafe := encrypt_spSafe v
      features := v.features }]) ++
  (if h : v.decWritten = 0 then [
    Spec.AesEcb.decryptApi.artifact X86.target {
      suffix := v.suffix
      code := v.dec.code
      verified := decrypt_free v h
      spSafe := v.decSpSafe
      features := v.features }]
  else [
    Spec.AesEcb.decryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesEcb.X86.wiped v.dec v.decWritten
      stack := 32
      verified := decrypt_verified v
      spSafe := decrypt_spSafe v
      features := v.features }])

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.AesEcb.X86
