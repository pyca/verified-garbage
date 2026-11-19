module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-OCB (RFC 7253) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesOcb.PPC64LE

def artifacts : List Artifact := [
  Spec.Ocb.initApi.artifact PPC64LE.target Proof.AesOcb.PPC64LE.Scrub.initReg,
  Spec.Ocb.sealApi.artifact PPC64LE.target Proof.AesOcb.PPC64LE.Scrub.sealReg,
  Spec.Ocb.openApi.artifact PPC64LE.target Proof.AesOcb.PPC64LE.Scrub.openReg]

end VG.Artifacts.AesOcb.PPC64LE
