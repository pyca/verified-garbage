module

public import VerifiedGarbage.Proof.Rc2.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Rc2.X86.Lit
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.X86.Stream.Lit

/-! # RC2 on x86 -/

@[expose] public section

namespace VG.Artifacts.Rc2.X86

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact X86.target Proof.Rc2.X86.Scrub.cbcInitReg,
  Spec.Rc2.cbcEncryptChainedApi.artifact X86.target Proof.Rc2.X86.Scrub.cbcEncryptChainedReg,
  Spec.Rc2.cbcDecryptChainedApi.artifact X86.target Proof.Rc2.X86.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.Rc2.X86
