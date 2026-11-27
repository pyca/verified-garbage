module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HMAC-SHA-512/224 (RFC 2104) on AArch64 -/

namespace VG.Artifacts.HmacSha512_224.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.MdHash.AArch64.sha512_224Variants.flatMap fun (v : Proof.Pbkdf2.Md.AArch64.MdHash) => [
    v.I.initAnyKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Pbkdf2.Md.AArch64.Fn.hmacInit v.H
      verified := Proof.Pbkdf2.Md.AArch64.MdHash.hmacInit_scrubbed v },
    v.I.finalizeApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Pbkdf2.Md.AArch64.Fn.hmacFin v.H
      verified := Proof.Pbkdf2.Md.AArch64.MdHash.hmacFin_scrubbed v }]

spec_apis artifacts

end VG.Artifacts.HmacSha512_224.AArch64
