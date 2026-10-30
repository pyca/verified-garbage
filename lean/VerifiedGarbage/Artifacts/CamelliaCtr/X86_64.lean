module

public import VerifiedGarbage.Proof.Camellia.X86_64.CtrVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CTR artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ctr
    stack := 3288
    verified := Proof.Camellia.X86_64.ctr_framed }]

end VG.Artifacts.CamelliaCtr.X86_64
