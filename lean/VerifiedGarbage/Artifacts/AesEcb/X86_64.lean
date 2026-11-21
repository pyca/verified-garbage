module

public import VerifiedGarbage.Proof.AesEcb.X86_64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86_64
public import VerifiedGarbage.Proof.Variants.Zeroize.X86_64

/-! # AES-ECB (NIST SP 800-38A §6.1) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesEcb.X86_64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86_64.variants.flatMap fun (v : Proof.Aes.X86_64.BlocksImpl) =>
    VG.Proof.Variants.Zeroize.X86_64.variants.flatMap fun (z : Proof.Zeroize.X86_64.ZeroizeImpl) =>
    (if h : v.encWritten = 0 then
      if z.suffix = "" then [Spec.AesEcb.encryptApi.artifact X86_64.target {
        suffix := v.suffix
        code := Impl.AesEcb.X86_64.Fn.plain v.level v.enc
        verified := Proof.AesEcb.X86_64.encryptPlain_scrubbed v h
        spSafe := Proof.AesEcb.X86_64.encryptPlain_spSafeFn v }]
      else []
    else if v.features.contains "avx" then
      if z.features = ["avx"] then [Spec.AesEcb.encryptApi.artifact X86_64.target {
        suffix := v.suffix
        code := Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.encWritten v.enc z.name z.code
        verified := Proof.AesEcb.X86_64.encryptWiped_scrubbed v z
        spSafe := Proof.AesEcb.X86_64.encryptWiped_spSafeFn v z }]
      else []
    else [Spec.AesEcb.encryptApi.artifact X86_64.target {
      suffix := v.suffix ++ z.suffix
      code := Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.encWritten v.enc z.name z.code
      verified := Proof.AesEcb.X86_64.encryptWiped_scrubbed v z
      spSafe := Proof.AesEcb.X86_64.encryptWiped_spSafeFn v z }]) ++
    (if h : v.decWritten = 0 then
      if z.suffix = "" then [Spec.AesEcb.decryptApi.artifact X86_64.target {
        suffix := v.suffix
        code := Impl.AesEcb.X86_64.Fn.plain v.level v.dec
        verified := Proof.AesEcb.X86_64.decryptPlain_scrubbed v h
        spSafe := Proof.AesEcb.X86_64.decryptPlain_spSafeFn v }]
      else []
    else if v.features.contains "avx" then
      if z.features = ["avx"] then [Spec.AesEcb.decryptApi.artifact X86_64.target {
        suffix := v.suffix
        code := Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.decWritten v.dec z.name z.code
        verified := Proof.AesEcb.X86_64.decryptWiped_scrubbed v z
        spSafe := Proof.AesEcb.X86_64.decryptWiped_spSafeFn v z }]
      else []
    else [Spec.AesEcb.decryptApi.artifact X86_64.target {
      suffix := v.suffix ++ z.suffix
      code := Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.decWritten v.dec z.name z.code
      verified := Proof.AesEcb.X86_64.decryptWiped_scrubbed v z
      spSafe := Proof.AesEcb.X86_64.decryptWiped_spSafeFn v z }])

end VG.Artifacts.AesEcb.X86_64
