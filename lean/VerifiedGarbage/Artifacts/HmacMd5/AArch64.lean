module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.Cold
public import VerifiedGarbage.Proof.Framework.EntryBranch
public import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.AnyKeyEntry
public import VerifiedGarbage.Proof.Sha256.AArch64.Compress
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Digest
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
public import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Digest
public import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # HMAC-MD5 (RFC 2104) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.HmacMd5.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.MdHash.AArch64.md5Variants.flatMap fun (v : Proof.Pbkdf2.Md.AArch64.MdHash) => [
    v.I.initAnyKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Proof.Pbkdf2.Md.AArch64.initCode v.H v.I
      stack := 16 + Proof.Pbkdf2.Md.AArch64.anyFrame v.I
      verified := v.hmacInitF },
    v.I.finalizeApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.StackScratch.AArch64.withStackScratch (Proof.Pbkdf2.Md.AArch64.hmacFrame v.I) .x4 v.H.hmacFin
      stack := 16 + Proof.Pbkdf2.Md.AArch64.hmacFrame v.I
      verified := v.hmacFinF }]

end VG.Artifacts.HmacMd5.AArch64
