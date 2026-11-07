module

public import VerifiedGarbage.Proof.Camellia.AArch64.CtrVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.CtrFinal
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Camellia.AArch64.Lit

/-! # Camellia-CTR artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.ctr
    stack := 3344
    verified := Proof.Camellia.AArch64.ctr_framed },
  Spec.Camellia.ctrFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 80 .x5 10 Impl.Camellia.AArch64.ctrFinal
    stack := 3424
    verified := Proof.Camellia.AArch64.CtrFinal.ctrFinal_framed }]

end VG.Artifacts.CamelliaCtr.AArch64
