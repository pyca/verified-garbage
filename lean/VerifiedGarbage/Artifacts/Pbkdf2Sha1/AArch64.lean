module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # PBKDF2-HMAC-SHA-1 (RFC 8018) on AArch64 -/

namespace VG.Artifacts.Pbkdf2Sha1.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.MdHash.AArch64.sha1Variants.flatMap fun (v : Proof.Pbkdf2.Md.AArch64.MdHash) => [
    v.I.pbkdf2Api.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Pbkdf2.Md.AArch64.Fn.pbkdf2 v.H
      verified := Proof.Pbkdf2.Md.AArch64.MdHash.pbkdf2_scrubbed v }]

spec_apis artifacts

end VG.Artifacts.Pbkdf2Sha1.AArch64
