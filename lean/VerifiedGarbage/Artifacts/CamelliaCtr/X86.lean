module

public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Camellia.X86.CtrLit

/-! # Camellia-CTR on x86 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.X86

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact X86.target Proof.Camellia.X86.Scrub.ctrReg,
  Spec.Camellia.ctrFinalApi.artifact X86.target Proof.Camellia.X86.Scrub.ctrFinalReg]

end VG.Artifacts.CamelliaCtr.X86
