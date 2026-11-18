module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.EcbVerified
public import VerifiedGarbage.Proof.Cast5.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Cast5.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Cast5.PPC64LE.Lit

/-! # CAST5 (RFC 2144) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Cast5.PPC64LE

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact PPC64LE.target Proof.Cast5.PPC64LE.Scrub.expandKeyReg,
  Spec.Cast5.ecbEncryptApi.artifact PPC64LE.target Proof.Cast5.PPC64LE.Scrub.ecbEncryptReg,
  Spec.Cast5.ecbDecryptApi.artifact PPC64LE.target Proof.Cast5.PPC64LE.Scrub.ecbDecryptReg]

end VG.Artifacts.Cast5.PPC64LE
