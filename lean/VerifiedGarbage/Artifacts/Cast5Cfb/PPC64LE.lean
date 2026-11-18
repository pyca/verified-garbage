module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Cast5.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalLit

/-! # CAST5-CFB64 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact PPC64LE.target Proof.Cast5.PPC64LE.Scrub.cfbEncryptReg,
  Spec.Cast5.cfbDecryptApi.artifact PPC64LE.target Proof.Cast5.PPC64LE.Scrub.cfbDecryptReg,
  Spec.Cast5.cfbEncryptFinalApi.artifact PPC64LE.target Proof.Cast5.PPC64LE.Scrub.cfbEncryptFinalReg,
  Spec.Cast5.cfbDecryptFinalApi.artifact PPC64LE.target Proof.Cast5.PPC64LE.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.Cast5Cfb.PPC64LE
