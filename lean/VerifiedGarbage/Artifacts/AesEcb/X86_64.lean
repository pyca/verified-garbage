module

public import VerifiedGarbage.Proof.AesEcb.X86_64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86_64
public import VerifiedGarbage.Proof.Variants.Zeroize.X86_64

/-! # AES-ECB (NIST SP 800-38A §6.1) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesEcb.X86_64

open VG.Proof.AesEcb.X86_64

def artifactsFor (v : Proof.Aes.X86_64.BlocksImpl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    List Artifact :=
  (if h : v.encWritten = 0 then (if z.suffix = "" then [
    Spec.AesEcb.encryptApi.artifact X86_64.target {
      suffix := v.suffix
      code := v.enc.code
      verified := encrypt_free v h
      spSafe := v.encSpSafe
      features := v.features }] else [])
  else if v.features.contains "avx" then (if z.features = ["avx"] then [
    Spec.AesEcb.encryptApi.artifact X86_64.target {
      suffix := v.suffix
      code := wiped z v.encWritten v.enc
      stack := 24
      verified := encrypt_verified v z
      spSafe := encrypt_spSafe v z
      features := v.features }] else [])
  else [
    Spec.AesEcb.encryptApi.artifact X86_64.target {
      suffix := v.suffix ++ z.suffix
      code := wiped z v.encWritten v.enc
      stack := 24
      verified := encrypt_verified v z
      spSafe := encrypt_spSafe v z
      features := v.features ++ z.features }]) ++
  (if h : v.decWritten = 0 then (if z.suffix = "" then [
    Spec.AesEcb.decryptApi.artifact X86_64.target {
      suffix := v.suffix
      code := v.dec.code
      verified := decrypt_free v h
      spSafe := v.decSpSafe
      features := v.features }] else [])
  else if v.features.contains "avx" then (if z.features = ["avx"] then [
    Spec.AesEcb.decryptApi.artifact X86_64.target {
      suffix := v.suffix
      code := wiped z v.decWritten v.dec
      stack := 24
      verified := decrypt_verified v z
      spSafe := decrypt_spSafe v z
      features := v.features }] else [])
  else [
    Spec.AesEcb.decryptApi.artifact X86_64.target {
      suffix := v.suffix ++ z.suffix
      code := wiped z v.decWritten v.dec
      stack := 24
      verified := decrypt_verified v z
      spSafe := decrypt_spSafe v z
      features := v.features ++ z.features }])

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86_64.variants.flatMap fun v => VG.Proof.Variants.Zeroize.X86_64.variants.flatMap fun v2 => artifactsFor v v2

end VG.Artifacts.AesEcb.X86_64
