module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Md5
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyInstances
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit

/-! # HMAC-MD5 (RFC 2104) on x86 -/

@[expose] public section

namespace VG.Artifacts.HmacMd5.X86

def artifacts : List Artifact := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact X86.target {
    code := Proof.Pbkdf2.Whole.X86.initCode Spec.Hmac.md5I Proof.Pbkdf2.Md.X86.md5M.hmacInit Proof.Pbkdf2.Whole.X86.md5F
    stack := 76 + Proof.Pbkdf2.Whole.X86.Any.anyFrame Spec.Hmac.md5I
    verified := Proof.Pbkdf2.Whole.X86.Any.md5_initF
    spSafe := Proof.Pbkdf2.Whole.X86.Any.md5_initSp },
  Spec.Hmac.md5I.finalizeApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.md5I) 5
      Proof.Pbkdf2.Md.X86.md5M.hmacFin
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.md5I
    verified := Proof.Pbkdf2.Md.X86.finFramed Proof.Pbkdf2.Md.X86.Instances.md5_finalize Proof.Hmac.md5_local
      Proof.Pbkdf2.Md.X86.md5_finFrameSat }]

end VG.Artifacts.HmacMd5.X86
