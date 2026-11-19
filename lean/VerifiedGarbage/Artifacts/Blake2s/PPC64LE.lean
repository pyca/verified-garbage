module

public import VerifiedGarbage.Proof.Blake2.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # BLAKE2s (RFC 7693) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Blake2s.PPC64LE

def artifacts : List Artifact := [
  Spec.Blake2.initSApi.artifact PPC64LE.target Proof.Blake2.PPC64LE.Scrub.initSReg,
  Spec.Blake2.updateSApi.artifact PPC64LE.target Proof.Blake2.PPC64LE.Scrub.updateSReg,
  Spec.Blake2.finalizeSApi.artifact PPC64LE.target Proof.Blake2.PPC64LE.Scrub.finalizeSReg]

end VG.Artifacts.Blake2s.PPC64LE
