module

public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-CMAC (NIST SP 800-38B) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CmacAes.PPC64LE

def artifacts : List Artifact := [
  Spec.Cmac.aesInitApi.artifact PPC64LE.target Proof.CmacAes.Stream.PPC64LE.Scrub.initReg,
  Spec.Cmac.aesAbsorbApi.artifact PPC64LE.target Proof.CmacAes.Stream.PPC64LE.Scrub.absorbReg,
  Spec.Cmac.aesFinishApi.artifact PPC64LE.target Proof.CmacAes.Stream.PPC64LE.Scrub.finishReg]

end VG.Artifacts.CmacAes.PPC64LE
