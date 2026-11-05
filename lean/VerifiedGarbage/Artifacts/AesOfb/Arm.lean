module

public import VerifiedGarbage.Proof.AesOfb.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-OFB (NIST SP 800-38A §6.4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesOfb.Arm

open VG.Proof.AesOfb.Arm

def artifacts : List Artifact := [
  Spec.Ofb.aesApi.artifact Arm.target {
    code := Impl.AesOfb.Arm.crypt
    stack := 8
    verified := Proof.AesOfb.keyed crypt_verified }]

end VG.Artifacts.AesOfb.Arm
