module

public import VerifiedGarbage.Proof.Aes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-CTR (NIST SP 800-38A §6.5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCtr.Arm

def artifacts : List Artifact := [
  Spec.Ctr.aesApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.ctr
    verified := Proof.Aes.Arm.Fn.ctr },
  Spec.Ctr.aesFinalApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.ctrFinal
    verified := Proof.Aes.Arm.Fn.ctrFinal }]

end VG.Artifacts.AesCtr.Arm
