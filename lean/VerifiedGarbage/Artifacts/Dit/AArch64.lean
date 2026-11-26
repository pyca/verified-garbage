module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Dit
import VerifiedGarbage.Proof.Dit.AArch64
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Data independent timing (FEAT_DIT) on AArch64 -/

namespace VG.Artifacts.Dit.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Dit.enterApi.artifact AArch64.target {
    code := Impl.Dit.AArch64.enter
    verified := Proof.Dit.AArch64.enter_scrubbed
    modeOk := Proof.Dit.AArch64.enter_mode },
  Spec.Dit.enterApi.artifact AArch64.target {
    suffix := "_dsb"
    code := Impl.Dit.AArch64.enterDsb
    verified := Proof.Dit.AArch64.enterDsb_scrubbed
    modeOk := Proof.Dit.AArch64.enterDsb_mode },
  Spec.Dit.enterApi.artifact AArch64.target {
    suffix := "_sb"
    code := Impl.Dit.AArch64.enterSb
    verified := Proof.Dit.AArch64.enterSb_scrubbed
    modeOk := Proof.Dit.AArch64.enterSb_mode },
  Spec.Dit.clearApi.artifact AArch64.target {
    code := Impl.Dit.AArch64.clear
    verified := Proof.Dit.AArch64.clear_scrubbed
    modeOk := Proof.Dit.AArch64.clear_mode }]

spec_apis artifacts

end VG.Artifacts.Dit.AArch64
