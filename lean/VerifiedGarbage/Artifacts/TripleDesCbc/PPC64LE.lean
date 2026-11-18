module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit

/-! # Triple DES-CBC on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact PPC64LE.target Proof.TripleDes.PPC64LE.Scrub.cbcEncryptChainedReg,
  Spec.TripleDes.cbcDecryptChainedApi.artifact PPC64LE.target Proof.TripleDes.PPC64LE.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.TripleDesCbc.PPC64LE
