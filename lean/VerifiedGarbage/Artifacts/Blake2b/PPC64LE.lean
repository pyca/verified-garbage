module

public import VerifiedGarbage.Proof.Blake2.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # BLAKE2b (RFC 7693) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Blake2b.PPC64LE

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact PPC64LE.target Proof.Blake2.PPC64LE.Scrub.initBReg,
  Spec.Blake2.updateBApi.artifact PPC64LE.target Proof.Blake2.PPC64LE.Scrub.updateBReg,
  Spec.Blake2.finalizeBApi.artifact PPC64LE.target Proof.Blake2.PPC64LE.Scrub.finalizeBReg]

end VG.Artifacts.Blake2b.PPC64LE
