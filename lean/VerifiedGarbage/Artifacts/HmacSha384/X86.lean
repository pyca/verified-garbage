module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha384
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyInstances
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit

/-! # HMAC-SHA-384 (RFC 2104) on x86 -/

@[expose] public section

namespace VG.Artifacts.HmacSha384.X86

def artifacts : List Artifact := [
  Spec.Hmac.sha384I.initAnyKeyApi.artifact X86.target {
    code := Proof.Pbkdf2.Whole.X86.initCode Spec.Hmac.sha384I Proof.Pbkdf2.Md.X86.sha384M.hmacInit Proof.Pbkdf2.Whole.X86.sha384F
    stack := 76 + Proof.Pbkdf2.Whole.X86.Any.anyFrame Spec.Hmac.sha384I
    verified := Proof.Pbkdf2.Whole.X86.Any.sha384_initF
    spSafe := Proof.Pbkdf2.Whole.X86.Any.sha384_initSp },
  Spec.Hmac.sha384I.finalizeApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha384I) 5
      Proof.Pbkdf2.Md.X86.sha384M.hmacFin
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha384I
    verified := Proof.Pbkdf2.Md.X86.finFramed Proof.Pbkdf2.Md.X86.Instances.sha384_finalize Proof.Hmac.sha384_local
      Proof.Pbkdf2.Md.X86.sha384_finFrameSat }]

end VG.Artifacts.HmacSha384.X86
