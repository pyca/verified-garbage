module

public import VerifiedGarbage.Proof.Sm4.X86.CtrVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86.CtrLit

/-! # SM4-CTR artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.X86

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ctr
    stack := 1516
    verified := Proof.Sm4.X86.Ctr.ctr_framed }]

end VG.Artifacts.Sm4Ctr.X86
