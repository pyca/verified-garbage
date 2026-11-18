module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FbFinalLit

/-! # Triple DES-CFB64 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact PPC64LE.target Proof.TripleDes.PPC64LE.Scrub.cfbEncryptReg,
  Spec.TripleDes.cfbDecryptApi.artifact PPC64LE.target Proof.TripleDes.PPC64LE.Scrub.cfbDecryptReg,
  Spec.TripleDes.cfbEncryptFinalApi.artifact PPC64LE.target Proof.TripleDes.PPC64LE.Scrub.cfbEncryptFinalReg,
  Spec.TripleDes.cfbDecryptFinalApi.artifact PPC64LE.target Proof.TripleDes.PPC64LE.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.TripleDesCfb.PPC64LE
