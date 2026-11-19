module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-SIV (RFC 5297) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesSiv.PPC64LE

def artifacts : List Artifact := [
  Spec.Siv.initApi.artifact PPC64LE.target Proof.AesSiv.PPC64LE.Scrub.initReg,
  Spec.Siv.encryptApi.artifact PPC64LE.target Proof.AesSiv.PPC64LE.Scrub.encryptReg,
  Spec.Siv.decryptApi.artifact PPC64LE.target Proof.AesSiv.PPC64LE.Scrub.decryptReg]

end VG.Artifacts.AesSiv.PPC64LE
