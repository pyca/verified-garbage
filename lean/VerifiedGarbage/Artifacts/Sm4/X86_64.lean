module

public import VerifiedGarbage.Proof.Sm4.X86_64.Scrub
public import VerifiedGarbage.Proof.Sm4.X86_64.KeyVerified
public import VerifiedGarbage.Proof.Sm4.X86_64.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Sm4.X86_64.Lit

/-! # SM4 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rdx 392 Impl.Sm4.X86_64.expandKey
    stack := 3144
    verified := Proof.Sm4.X86_64.expandKey_framed },
  Spec.Sm4.ecbEncryptApi.artifact X86_64.target Proof.Sm4.X86_64.Scrub.ecbEncryptReg,
  Spec.Sm4.ecbDecryptApi.artifact X86_64.target Proof.Sm4.X86_64.Scrub.ecbDecryptReg]

end VG.Artifacts.Sm4.X86_64
