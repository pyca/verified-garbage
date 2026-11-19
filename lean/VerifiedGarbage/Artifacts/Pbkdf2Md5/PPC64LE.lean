module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # PBKDF2-HMAC-MD5 (RFC 8018) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Md5.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.md5I.pbkdf2Api.artifact PPC64LE.target Proof.Pbkdf2.Whole.PPC64LE.Scrub.md5Pbkdf2Reg]

end VG.Artifacts.Pbkdf2Md5.PPC64LE
