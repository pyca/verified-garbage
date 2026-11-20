module

public import VerifiedGarbage.Proof.Aes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-OFB (NIST SP 800-38A §6.4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesOfb.Arm

def artifacts : List Artifact := [
  Spec.Ofb.aesApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.ofb
    verified := .scrubbed Proof.Aes.Arm.Fn.ofb },
  Spec.Ofb.aesFinalApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.ofbFinal
    verified := .scrubbed Proof.Aes.Arm.Fn.ofbFinal }]

end VG.Artifacts.AesOfb.Arm
