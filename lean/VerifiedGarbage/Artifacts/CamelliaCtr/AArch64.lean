module

public import VerifiedGarbage.Impl.Camellia.AArch64.CtrFinal
public import VerifiedGarbage.Proof.Camellia.AArch64.CtrScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Camellia.CtrFinal
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Camellia-CTR on AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.ctr
    verified := .scrubbed Proof.Camellia.AArch64.Fn.ctr },
  Spec.Camellia.ctrFinalApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.ctrFinal
    verified := .scrubbed Proof.Camellia.AArch64.Fn.ctrFinal }]

end VG.Artifacts.CamelliaCtr.AArch64
