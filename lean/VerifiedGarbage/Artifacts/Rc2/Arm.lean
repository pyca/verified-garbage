module

public import VerifiedGarbage.Proof.Rc2.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # RC2 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Rc2.Arm

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact Arm.target {
    code := Impl.Rc2.Arm.Fn.cbcInit
    verified := .scrubbed Proof.Rc2.Arm.Fn.cbcInit },
  Spec.Rc2.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Rc2.Arm.Fn.cbcEncryptChained
    verified := .scrubbed Proof.Rc2.Arm.Fn.cbcEncryptChained },
  Spec.Rc2.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Rc2.Arm.Fn.cbcDecryptChained
    verified := .scrubbed Proof.Rc2.Arm.Fn.cbcDecryptChained }]

end VG.Artifacts.Rc2.Arm
