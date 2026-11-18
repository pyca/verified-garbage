module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalLit

/-! # SM4-CFB128 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact PPC64LE.target Proof.Sm4.PPC64LE.Scrub.cfbEncryptReg,
  Spec.Sm4.cfbDecryptApi.artifact PPC64LE.target Proof.Sm4.PPC64LE.Scrub.cfbDecryptReg,
  Spec.Sm4.cfbEncryptFinalApi.artifact PPC64LE.target Proof.Sm4.PPC64LE.Scrub.cfbEncryptFinalReg,
  Spec.Sm4.cfbDecryptFinalApi.artifact PPC64LE.target Proof.Sm4.PPC64LE.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.Sm4Cfb.PPC64LE
