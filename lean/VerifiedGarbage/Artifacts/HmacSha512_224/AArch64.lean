module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # HMAC-SHA-512/224 (RFC 2104) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_224.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.MdHash.AArch64.sha512_224Variants.flatMap fun (v : Proof.Pbkdf2.Md.AArch64.MdHash) => [
    v.I.initAnyKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Pbkdf2.Md.AArch64.Fn.hmacInit v.H
      verified := .scrubbed v.hmacInit_scrubbed },
    v.I.finalizeApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Pbkdf2.Md.AArch64.Fn.hmacFin v.H
      verified := .scrubbed v.hmacFin_scrubbed }]

end VG.Artifacts.HmacSha512_224.AArch64
