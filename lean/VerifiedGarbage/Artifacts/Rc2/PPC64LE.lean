module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Block
public import VerifiedGarbage.Proof.Rc2.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Chained
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RC2 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Rc2.PPC64LE

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact PPC64LE.target Proof.Rc2.PPC64LE.Scrub.cbcInitReg,
  Spec.Rc2.cbcEncryptChainedApi.artifact PPC64LE.target Proof.Rc2.PPC64LE.Scrub.cbcEncryptChainedReg,
  Spec.Rc2.cbcDecryptChainedApi.artifact PPC64LE.target Proof.Rc2.PPC64LE.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.Rc2.PPC64LE
