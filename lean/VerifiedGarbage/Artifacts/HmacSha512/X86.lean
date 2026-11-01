module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyInstances
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit

/-! # HMAC-SHA-512 (RFC 2104) on x86 -/

@[expose] public section

namespace VG.Artifacts.HmacSha512.X86

def artifacts : List Artifact := [
  Spec.Hmac.sha512I.initAnyKeyApi.artifact X86.target {
    code := Proof.Pbkdf2.Whole.X86.initCode Spec.Hmac.sha512I Proof.Pbkdf2.Md.X86.sha512M'.hmacInit Proof.Pbkdf2.Whole.X86.sha512F
    stack := 76 + Proof.Pbkdf2.Whole.X86.Any.anyFrame Spec.Hmac.sha512I
    verified := Proof.Pbkdf2.Whole.X86.Any.sha512_initF
    spSafe := Proof.Pbkdf2.Whole.X86.Any.sha512_initSp },
  Spec.Hmac.sha512I.finalizeApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha512I) 5
      Proof.Pbkdf2.Md.X86.sha512M'.hmacFin
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha512I
    verified := Proof.Pbkdf2.Md.X86.finFramed Proof.Pbkdf2.Md.X86.Instances.sha512_finalize Proof.Hmac.sha512_local
      Proof.Pbkdf2.Md.X86.sha512_finFrameSat }]

end VG.Artifacts.HmacSha512.X86
