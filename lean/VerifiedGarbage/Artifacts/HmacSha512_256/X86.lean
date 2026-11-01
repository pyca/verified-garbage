module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512_256
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyInstances
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit

/-! # HMAC-SHA-512/256 (RFC 2104) on x86 -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_256.X86

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.initAnyKeyApi.artifact X86.target {
    code := Proof.Pbkdf2.Whole.X86.initCode Spec.Hmac.sha512_256I Proof.Pbkdf2.Md.X86.sha512_256M.hmacInit Proof.Pbkdf2.Whole.X86.sha512_256F
    stack := 76 + Proof.Pbkdf2.Whole.X86.Any.anyFrame Spec.Hmac.sha512_256I
    verified := Proof.Pbkdf2.Whole.X86.Any.sha512_256_initF
    spSafe := Proof.Pbkdf2.Whole.X86.Any.sha512_256_initSp },
  Spec.Hmac.sha512_256I.finalizeApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha512_256I) 5
      Proof.Pbkdf2.Md.X86.sha512_256M.hmacFin
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha512_256I
    verified := Proof.Pbkdf2.Md.X86.finFramed Proof.Pbkdf2.Md.X86.Instances.sha512_256_finalize Proof.Hmac.sha512_256_local
      Proof.Pbkdf2.Md.X86.sha512_256_finFrameSat }]

end VG.Artifacts.HmacSha512_256.X86
