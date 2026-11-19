module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Lit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.PPC64LE

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact PPC64LE.target Proof.CmacTripleDes.Stream.PPC64LE.Scrub.initReg,
  Spec.Cmac.tdesAbsorbApi.artifact PPC64LE.target Proof.CmacTripleDes.Stream.PPC64LE.Scrub.absorbReg,
  Spec.Cmac.tdesFinishApi.artifact PPC64LE.target Proof.CmacTripleDes.Stream.PPC64LE.Scrub.finishReg]

end VG.Artifacts.CmacTripleDes.PPC64LE
