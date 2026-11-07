module

public import VerifiedGarbage.Proof.Dit.AArch64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Entering and leaving data independent timing (PSTATE.DIT) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Dit.AArch64

def artifacts : List Artifact := [
  Spec.Dit.enterApi.artifact AArch64.target {
    code := Impl.Dit.AArch64.enter
    verified := Proof.Dit.AArch64.enter_verified
    features := ["dit"] },
  Spec.Dit.clearApi.artifact AArch64.target {
    code := Impl.Dit.AArch64.clear
    verified := Proof.Dit.AArch64.clear_verified
    features := ["dit"] }]

end VG.Artifacts.Dit.AArch64
