module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Spec.Camellia.CtrFinal
import VerifiedGarbage.Impl.Camellia.AArch64.CtrFinal
import VerifiedGarbage.Proof.Camellia.AArch64.CtrScrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CTR on AArch64 -/

namespace VG.Artifacts.CamelliaCtr.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Camellia.ctrApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.ctr
    verified := Proof.Camellia.AArch64.Fn.ctr },
  Spec.Camellia.ctrFinalApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.ctrFinal
    verified := Proof.Camellia.AArch64.Fn.ctrFinal }]

spec_apis artifacts

end VG.Artifacts.CamelliaCtr.AArch64
