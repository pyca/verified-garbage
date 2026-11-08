module

public import VerifiedGarbage.Proof.AesCbc.X86_64.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # AES-CBC (NIST SP 800-38A §6.2) on x86-64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.Zeroize.X86_64.AesCbc

open VG.Proof.AesCbc.X86_64

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    List Artifact :=
  (if Caller.vaes v then [] else if Caller.hardware v then (if z.suffix = "" then [
    Spec.Cbc.aesEncryptApi.artifact X86_64.target {
      suffix := v.suffix
      code := Caller.encrypt v
      stack := 8
      verified := Proof.AesCbc.encrypt_keyed (Caller.verified v)
      spSafe := Caller.spSafe v
      written := Caller.written v
      writtenOk := Caller.written_ok v
      features := Caller.encFeatures v }] else []) else [
    Spec.Cbc.aesEncryptApi.artifact X86_64.target {
      suffix := v.suffix ++ z.suffix
      code := Wiped.encrypt v z
      stack := 32
      verified := Wiped.encrypt_verified v z
      spSafe := Wiped.encrypt_spSafe v z
      features := Caller.encFeatures v ++ z.features }]) ++
  if Caller.vaes v then (if z.suffix = "" then [] else [
    Spec.Cbc.aesDecryptApi.artifact X86_64.target {
      suffix := v.suffix
      code := Wiped.decrypt v z
      stack := 32
      verified := Wiped.decrypt_verified v z
      spSafe := Wiped.decrypt_spSafe v z
      features := Caller.decFeatures v }])
  else [
    Spec.Cbc.aesDecryptApi.artifact X86_64.target {
      suffix := v.suffix ++ z.suffix
      code := Wiped.decrypt v z
      stack := 32
      verified := Wiped.decrypt_verified v z
      spSafe := Wiped.decrypt_spSafe v z
      features := Caller.decFeatures v ++ z.features }]

end VG.Generic.AesBlocks.Zeroize.X86_64.AesCbc
