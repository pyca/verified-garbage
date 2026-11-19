module

public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # ChaCha20 (RFC 8439) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.PPC64LE

def artifacts : List Artifact := [
  Spec.ChaCha20.initApi.artifact PPC64LE.target Proof.ChaCha20.PPC64LE.Scrub.initReg,
  Spec.ChaCha20.setNonceApi.artifact PPC64LE.target Proof.ChaCha20.PPC64LE.Scrub.setNonceReg,
  Spec.ChaCha20.applyApi.artifact PPC64LE.target Proof.ChaCha20.PPC64LE.Scrub.applyReg]

end VG.Artifacts.ChaCha20.PPC64LE
