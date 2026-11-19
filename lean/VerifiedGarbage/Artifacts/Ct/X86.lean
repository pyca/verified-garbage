module

public import VerifiedGarbage.Proof.Ct.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # Constant-time byte comparison on x86 -/

@[expose] public section

namespace VG.Artifacts.Ct.X86
open VG.X86

def artifacts : List Artifact := [
  Spec.Ct.eqApi.artifact target Proof.Ct.X86.Scrub.eqReg]
end VG.Artifacts.Ct.X86
