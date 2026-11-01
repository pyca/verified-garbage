module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeySha256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-224 (RFC 2104) on x86, for every x86 SHA-256 backend -/

@[expose] public section

namespace VG.Generic.Sha256.X86.HmacSha224

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  Spec.Hmac.sha224I.initAnyKeyApi.artifact X86.target {
    suffix := v.suffix
    code := Proof.Pbkdf2.Whole.X86.initCode Spec.Hmac.sha224I v.M224.hmacInit v.F224
    stack := 76 + Proof.Pbkdf2.Whole.X86.Any.anyFrame Spec.Hmac.sha224I
    verified := Proof.Pbkdf2.Whole.X86.Any.sha224_initF v
    spSafe := Proof.Pbkdf2.Whole.X86.Any.sha224_initSp v
    features := v.features },
  Spec.Hmac.sha224I.finalizeApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha224I) 5
      v.M224.hmacFin
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha224I
    verified := Proof.Pbkdf2.Md.X86.finFramed v.hmacFin224 Proof.Hmac.sha224_local Proof.Pbkdf2.Md.X86.sha224_finFrameSat
      (Proof.Pbkdf2.Md.X86.noEsp_of v.finalize224NoSp) v.finalize224Stack
    spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.fin224Sp
    features := v.features }]

end VG.Generic.Sha256.X86.HmacSha224
