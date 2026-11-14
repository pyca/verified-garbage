module

public import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.KeyVerified
import VerifiedGarbage.Proof.Cast5.X86_64.Lit
public import VerifiedGarbage.Proof.Cast5.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # CAST5 (RFC 2144) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Cast5.X86_64

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact X86_64.target Proof.Cast5.X86_64.Scrub.expandKeyReg,
  Spec.Cast5.ecbEncryptApi.artifact X86_64.target Proof.Cast5.X86_64.Scrub.ecbEncryptReg,
  Spec.Cast5.ecbDecryptApi.artifact X86_64.target Proof.Cast5.X86_64.Scrub.ecbDecryptReg]

end VG.Artifacts.Cast5.X86_64
