module

public import VerifiedGarbage.Proof.Sm4.X86_64.CtrVerified
public import VerifiedGarbage.Proof.Sm4.X86_64.CtrFinal
public import VerifiedGarbage.Proof.Sm4.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit

/-! # SM4-CTR on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact X86_64.target Proof.Sm4.X86_64.Scrub.ctrReg,
  Spec.Sm4.ctrFinalApi.artifact X86_64.target Proof.Sm4.X86_64.Scrub.ctrFinalReg]

end VG.Artifacts.Sm4Ctr.X86_64
