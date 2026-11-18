module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Verified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

/-! # SM4 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact PPC64LE.target Proof.Sm4.PPC64LE.Scrub.expandKeyReg,
  Spec.Sm4.ecbEncryptApi.artifact PPC64LE.target Proof.Sm4.PPC64LE.Scrub.ecbEncryptReg,
  Spec.Sm4.ecbDecryptApi.artifact PPC64LE.target Proof.Sm4.PPC64LE.Scrub.ecbDecryptReg]

end VG.Artifacts.Sm4.PPC64LE
