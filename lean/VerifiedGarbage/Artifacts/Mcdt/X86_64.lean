module

public import VerifiedGarbage.Proof.Mcdt.X86_64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Intel's MXCSR mitigation of MCDT on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Mcdt.X86_64

def artifacts : List Artifact := [
  Spec.Mcdt.enterApi.artifact X86_64.target Proof.Mcdt.X86_64.enterReg]

end VG.Artifacts.Mcdt.X86_64
