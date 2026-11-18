module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Camellia.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalLit

/-! # Camellia-CFB128 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact PPC64LE.target Proof.Camellia.PPC64LE.Scrub.cfbEncReg,
  Spec.Camellia.cfbDecryptApi.artifact PPC64LE.target Proof.Camellia.PPC64LE.Scrub.cfbDecReg,
  Spec.Camellia.cfbEncryptFinalApi.artifact PPC64LE.target Proof.Camellia.PPC64LE.Scrub.cfbEncFinalReg,
  Spec.Camellia.cfbDecryptFinalApi.artifact PPC64LE.target Proof.Camellia.PPC64LE.Scrub.cfbDecFinalReg]

end VG.Artifacts.CamelliaCfb.PPC64LE
