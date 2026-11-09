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

/-! # PBKDF2-HMAC-SHA-224 (RFC 8018) on AArch64: the iteration and the whole derivation -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha224.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.MdHash.AArch64.sha224Variants.flatMap fun (v : Proof.Pbkdf2.Md.AArch64.MdHash) => [
    v.I.pbkdf2Api.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.StackScratch.AArch64.withStackScratch (Proof.Pbkdf2.Md.AArch64.pbkdf2Frame v.I) .x7 v.H.pbkdf2
      stack := 16 + Proof.Pbkdf2.Md.AArch64.pbkdf2Frame v.I
      verified := v.pbkdf2F }]

end VG.Artifacts.Pbkdf2Sha224.AArch64
