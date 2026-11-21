module

public import VerifiedGarbage.Impl.AesCbc.X86_64.Fn
public import VerifiedGarbage.Proof.AesCbc.X86_64.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86_64
public import VerifiedGarbage.Proof.Variants.Zeroize.X86_64

/-! # AES-CBC (NIST SP 800-38A §6.2) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesCbc.X86_64

def direct : List Artifact := [
  Spec.Cbc.aesDecryptApi.artifact VG.X86_64.target {
    suffix := "_vaes_avx512"
    code := Impl.AesCbc.X86_64.Fn.decryptVaes512 .avx Proof.Zeroize.X86_64.ZeroizeImpl.avx.name
      Proof.Zeroize.X86_64.ZeroizeImpl.avx.code
    verified := Proof.AesCbc.X86_64.Wiped.decryptVaes512_scrubbedFn }]

end VG.Artifacts.AesCbc.X86_64

namespace VG.Artifacts.AesCbc.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.AesBlocks.X86_64.variants.flatMap fun (v : Proof.Aes.X86_64.BlocksImpl) =>
    VG.Proof.Variants.Zeroize.X86_64.variants.flatMap fun (z : Proof.Zeroize.X86_64.ZeroizeImpl) =>
    (if Proof.AesCbc.X86_64.Caller.vaes v then []
    else if h : Proof.AesCbc.X86_64.Caller.hardware v then
      if z.suffix = "" then [Spec.Cbc.aesEncryptApi.artifact X86_64.target {
        suffix := v.suffix
        code := Impl.AesCbc.X86_64.Fn.encryptFree .sse
        verified := Proof.AesCbc.X86_64.Wiped.encryptFree_scrubbed v h
        spSafe := Proof.AesCbc.X86_64.Wiped.encryptFree_spSafeFn }]
      else []
    else [Spec.Cbc.aesEncryptApi.artifact X86_64.target {
      suffix := v.suffix ++ z.suffix
      code := Impl.AesCbc.X86_64.Fn.encrypt (v.level.join z.level) (Proof.AesCbc.X86_64.Caller.hardware v) v.enc v.suffix
        z.name z.code
      verified := Proof.AesCbc.X86_64.Wiped.encrypt_scrubbedFn v z
      spSafe := Proof.AesCbc.X86_64.Wiped.encrypt_spSafeFn v z }]) ++
    (if Proof.AesCbc.X86_64.Caller.vaes v then
      if z.suffix = "" then []
      else [Spec.Cbc.aesDecryptApi.artifact X86_64.target {
        suffix := v.suffix
        code := Impl.AesCbc.X86_64.Fn.decrypt (Proof.AesCbc.X86_64.Wiped.decLv v z) (Proof.AesCbc.X86_64.Caller.vaes v)
          (Proof.AesCbc.X86_64.Caller.hardware v) v.dec v.suffix z.name z.code
        verified := Proof.AesCbc.X86_64.Wiped.decrypt_scrubbedFn v z
        spSafe := Proof.AesCbc.X86_64.Wiped.decrypt_spSafeFn v z }]
    else [Spec.Cbc.aesDecryptApi.artifact X86_64.target {
      suffix := v.suffix ++ z.suffix
      code := Impl.AesCbc.X86_64.Fn.decrypt (Proof.AesCbc.X86_64.Wiped.decLv v z) (Proof.AesCbc.X86_64.Caller.vaes v)
        (Proof.AesCbc.X86_64.Caller.hardware v) v.dec v.suffix z.name z.code
      verified := Proof.AesCbc.X86_64.Wiped.decrypt_scrubbedFn v z
      spSafe := Proof.AesCbc.X86_64.Wiped.decrypt_spSafeFn v z }]))

end VG.Artifacts.AesCbc.X86_64
