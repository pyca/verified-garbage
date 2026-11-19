module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Scrub
import VerifiedGarbage.Proof.CmacTripleDes.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86 -/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.X86

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact X86.target Proof.CmacTripleDes.Stream.X86.Scrub.initReg,
  Spec.Cmac.tdesAbsorbApi.artifact X86.target Proof.CmacTripleDes.Stream.X86.Scrub.absorbReg,
  Spec.Cmac.tdesFinishApi.artifact X86.target Proof.CmacTripleDes.Stream.X86.Scrub.finishReg]

end VG.Artifacts.CmacTripleDes.X86
