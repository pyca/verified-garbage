module

public import VerifiedGarbage.Proof.Camellia.AArch64.CtrVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.CtrFinal
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Camellia.AArch64.Lit
public import VerifiedGarbage.Proof.Camellia.AArch64.CtrScrub

/-! # Camellia-CTR on AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
    code := Impl.StackScratch.AArch64.withStackScratch 3344 .x5 Impl.Camellia.AArch64.ctr
    verified := Proof.Camellia.AArch64.ctr_framed } Proof.Camellia.AArch64.CtrScrub.ctrOk),
  Spec.Camellia.ctrFinalApi.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 80 .x5 10 Impl.Camellia.AArch64.ctrFinal
    verified := Proof.Camellia.AArch64.CtrFinal.ctrFinal_framed } Proof.Camellia.AArch64.CtrScrub.ctrFinalOk)]

end VG.Artifacts.CamelliaCtr.AArch64
