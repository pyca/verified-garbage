module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # PBKDF2-HMAC-SHA-256 (RFC 8018) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha256.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.MdHash.AArch64.sha256Variants.flatMap fun (v : Proof.Pbkdf2.Md.AArch64.MdHash) => [
    v.I.pbkdf2Api.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Pbkdf2.Md.AArch64.Fn.pbkdf2 v.H
      verified := Proof.Pbkdf2.Md.AArch64.MdHash.pbkdf2_scrubbed v }]

end VG.Artifacts.Pbkdf2Sha256.AArch64
