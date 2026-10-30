module

public import VerifiedGarbage.Proof.Sm4.X86_64.CtrVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit

/-! # SM4-CTR artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ctr
    stack := 3216
    verified := Proof.Sm4.X86_64.ctr_framed }]

end VG.Artifacts.Sm4Ctr.X86_64
