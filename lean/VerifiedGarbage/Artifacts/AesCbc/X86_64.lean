module

public import VerifiedGarbage.Proof.AesCbc.X86_64.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86_64
public import VerifiedGarbage.Proof.Variants.Zeroize.X86_64

/-! # AES-CBC decryption with thirty-two AVX-512 VAES states -/

@[expose] public section

namespace VG.Artifacts.AesCbc.X86_64

def direct : List Artifact := [
  Spec.Cbc.aesDecryptApi.artifact VG.X86_64.target {
    suffix := "_vaes_avx512"
    code := Proof.AesCbc.X86_64.Wiped.decryptVaes512
    stack := 32
    spSafe := Proof.AesCbc.X86_64.Wiped.decryptVaes512_spSafe
    verified := Proof.AesCbc.X86_64.Wiped.decryptVaes512_verified
    features := ["aes","avx","avx2","vaes","avx512f"] }]

end VG.Artifacts.AesCbc.X86_64

-- AES-CBC (NIST SP 800-38A §6.2) on x86-64
namespace VG.Artifacts.AesCbc.X86_64.AesBlocksZeroize

open VG.Proof.AesCbc.X86_64

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    List Artifact :=
  (if Caller.vaes v then [] else if h : Caller.hardware v then (if z.suffix = "" then [
    Spec.Cbc.aesEncryptApi.artifact X86_64.target {
      suffix := v.suffix
      code := Caller.encrypt v
      stack := 8
      verified := Wiped.encrypt_free_scrubbed v h
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

end VG.Artifacts.AesCbc.X86_64.AesBlocksZeroize

namespace VG.Artifacts.AesCbc.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.AesBlocks.X86_64.variants.flatMap fun v => VG.Proof.Variants.Zeroize.X86_64.variants.flatMap fun v2 => AesBlocksZeroize.artifacts v v2)

end VG.Artifacts.AesCbc.X86_64
