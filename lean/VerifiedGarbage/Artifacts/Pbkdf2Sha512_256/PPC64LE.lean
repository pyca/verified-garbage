module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # PBKDF2-HMAC-SHA-512/256 (RFC 8018) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha512_256.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.pbkdf2Api.artifact PPC64LE.target Proof.Pbkdf2.Whole.PPC64LE.Scrub.sha512_256Pbkdf2Reg]

end VG.Artifacts.Pbkdf2Sha512_256.PPC64LE
