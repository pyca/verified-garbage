module

public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86_64.Frame
public import VerifiedGarbage.Proof.Aes.X86_64.Scrub
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # AES (FIPS 197) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Aes.X86_64

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact X86_64.target Proof.Aes.X86_64.Scrub.expandKeyAesniReg,
  Spec.Aes.expandKeyApi.artifact X86_64.target Proof.Aes.X86_64.Scrub.expandKeyReg]

end VG.Artifacts.Aes.X86_64
