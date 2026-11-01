module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512_224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyInstances
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit

/-! # HMAC-SHA-512/224 (RFC 2104) on x86 -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_224.X86

def artifacts : List Artifact := [
  Spec.Hmac.sha512_224I.initAnyKeyApi.artifact X86.target {
    code := Proof.Pbkdf2.Whole.X86.initCode Spec.Hmac.sha512_224I Proof.Pbkdf2.Md.X86.sha512_224M.hmacInit Proof.Pbkdf2.Whole.X86.sha512_224F
    stack := 76 + Proof.Pbkdf2.Whole.X86.Any.anyFrame Spec.Hmac.sha512_224I
    verified := Proof.Pbkdf2.Whole.X86.Any.sha512_224_initF
    spSafe := Proof.Pbkdf2.Whole.X86.Any.sha512_224_initSp },
  Spec.Hmac.sha512_224I.finalizeApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha512_224I) 5
      Proof.Pbkdf2.Md.X86.sha512_224M.hmacFin
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha512_224I
    verified := Proof.Pbkdf2.Md.X86.finFramed Proof.Pbkdf2.Md.X86.Instances.sha512_224_finalize Proof.Hmac.sha512_224_local
      Proof.Pbkdf2.Md.X86.sha512_224_finFrameSat }]

end VG.Artifacts.HmacSha512_224.X86
