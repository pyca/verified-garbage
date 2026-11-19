module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.X86.Print

/-! # PBKDF2-HMAC-MD5 (RFC 8018) on x86 -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Md5.X86

def artifacts : List Artifact := [
  Spec.Hmac.md5I.pbkdf2Api.artifact X86.target Proof.Pbkdf2.Whole.X86.Scrub.md5Reg]

end VG.Artifacts.Pbkdf2Md5.X86
