module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Verified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Lit

/-! # Triple DES on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDes.PPC64LE

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact PPC64LE.target Proof.TripleDes.PPC64LE.Scrub.expandKeyReg,
  Spec.TripleDes.ecbEncryptApi.artifact PPC64LE.target Proof.TripleDes.PPC64LE.Scrub.ecbEncryptReg,
  Spec.TripleDes.ecbDecryptApi.artifact PPC64LE.target Proof.TripleDes.PPC64LE.Scrub.ecbDecryptReg]

end VG.Artifacts.TripleDes.PPC64LE
