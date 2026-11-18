module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalLit

/-! # Blowfish-CFB64 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact PPC64LE.target Proof.Blowfish.PPC64LE.Scrub.cfbEncryptReg,
  Spec.Blowfish.cfbDecryptApi.artifact PPC64LE.target Proof.Blowfish.PPC64LE.Scrub.cfbDecryptReg,
  Spec.Blowfish.cfbEncryptFinalApi.artifact PPC64LE.target Proof.Blowfish.PPC64LE.Scrub.cfbEncryptFinalReg,
  Spec.Blowfish.cfbDecryptFinalApi.artifact PPC64LE.target Proof.Blowfish.PPC64LE.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.BlowfishCfb.PPC64LE
