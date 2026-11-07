module

public import VerifiedGarbage.Proof.AesCtr.Arm.Verified
public import VerifiedGarbage.Proof.AesCtr.Arm.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-CTR (NIST SP 800-38A §6.5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCtr.Arm

open VG.Proof.AesCtr.Arm

def artifacts : List Artifact := [
  Spec.Ctr.aesApi.artifact Arm.target {
    code := Impl.AesCtr.Arm.crypt
    stack := 8
    verified := Proof.AesCtr.keyed crypt_verified },
  Spec.Ctr.aesFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 72 2 14 Impl.AesCtr.Arm.cryptFinal
    stack := 88
    verified := Proof.AesCtr.final_keyed cryptFinal_framed }]

end VG.Artifacts.AesCtr.Arm
