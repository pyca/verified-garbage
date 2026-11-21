module

public import VerifiedGarbage.Proof.Blake2.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # BLAKE2s (RFC 7693) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Blake2s.Arm

def artifacts : List Artifact := [
  Spec.Blake2.initSApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Fn.initS
    verified := Proof.Blake2.Arm.Fn.initS },
  Spec.Blake2.updateSApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Fn.updateS
    verified := Proof.Blake2.Arm.Fn.updateS },
  Spec.Blake2.finalizeSApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Fn.finalizeS
    verified := Proof.Blake2.Arm.Fn.finalizeS }]

end VG.Artifacts.Blake2s.Arm
