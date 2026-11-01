module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeySha256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-256 (RFC 2104) on x86, for every x86 SHA-256 backend -/

@[expose] public section

namespace VG.Generic.Sha256.X86.Hmac

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  Spec.Hmac.sha256I.initAnyKeyApi.artifact X86.target {
    suffix := v.suffix
    code := Proof.Pbkdf2.Whole.X86.initCode Spec.Hmac.sha256I v.M.hmacInit v.F
    stack := 76 + Proof.Pbkdf2.Whole.X86.Any.anyFrame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Whole.X86.Any.sha256_initF v
    spSafe := Proof.Pbkdf2.Whole.X86.Any.sha256_initSp v
    features := v.features },
  Spec.Hmac.sha256I.finalizeApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha256I) 5
      v.M.hmacFin
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Md.X86.finFramed v.hmacFin Proof.Hmac.sha256_local Proof.Pbkdf2.Md.X86.sha256_finFrameSat
      (Proof.Pbkdf2.Md.X86.noEsp_of v.finalizeNoSp) v.finalizeStack
    spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.finSp
    features := v.features }]

end VG.Generic.Sha256.X86.Hmac
