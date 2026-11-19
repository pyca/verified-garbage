module

public import VerifiedGarbage.Proof.Argon2.PPC64LE.Compress
public import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.CT
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Verified
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # Argon2 (RFC 9106) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Argon2.PPC64LE

def artifacts : List Artifact := [
  Spec.Argon2.deriveApi.artifact PPC64LE.target Proof.Argon2.PPC64LE.Scrub.deriveReg]

end VG.Artifacts.Argon2.PPC64LE
