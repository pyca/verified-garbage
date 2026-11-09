module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeySha1
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeySha256
public import VerifiedGarbage.Proof.Variants.Sha256.X86

/-! # HMAC-SHA-1 (RFC 2104) on x86, for every x86 SHA-1 backend -/

@[expose] public section

namespace VG.Artifacts.Hmac.X86.Sha1

def artifacts (v : Proof.Sha1.X86.Variants.Backend) : List Artifact := [
  Spec.Hmac.sha1I.initAnyKeyApi.artifact X86.target {
    suffix := v.suffix
    code := Proof.Pbkdf2.Whole.X86.initCode Spec.Hmac.sha1I v.M.hmacInit v.F
    stack := 76 + Proof.Pbkdf2.Whole.X86.Any.anyFrame Spec.Hmac.sha1I
    verified := Proof.Pbkdf2.Whole.X86.Any.sha1_initF v
    spSafe := Proof.Pbkdf2.Whole.X86.Any.sha1_initSp v
    features := v.features },
  Spec.Hmac.sha1I.finalizeApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha1I) 5
      v.M.hmacFin
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha1I
    verified := Proof.Pbkdf2.Md.X86.finFramed v.hmacFin Proof.Hmac.sha1_local Proof.Pbkdf2.Md.X86.sha1_finFrameSat
      (Proof.Pbkdf2.Md.X86.noEsp_of v.finalizeNoSp) v.finalizeStack
    spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.finSp
    features := v.features }]

end VG.Artifacts.Hmac.X86.Sha1

-- HMAC-SHA-256 (RFC 2104) on x86, for every x86 SHA-256 backend
namespace VG.Artifacts.Hmac.X86.Sha256

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

end VG.Artifacts.Hmac.X86.Sha256

namespace VG.Artifacts.Hmac.X86

def artifacts : List Artifact :=
  (VG.Proof.Variants.Sha1.X86.variants.flatMap fun v => Sha1.artifacts v) ++
  (VG.Proof.Variants.Sha256.X86.variants.flatMap fun v => Sha256.artifacts v)

end VG.Artifacts.Hmac.X86
