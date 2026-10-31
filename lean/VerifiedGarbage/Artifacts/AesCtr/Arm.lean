module

public import VerifiedGarbage.Proof.AesCtr.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CTR (NIST SP 800-38A §6.5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCtr.Arm

open VG.Proof.AesCtr.Arm

def artifacts : List Artifact := [
  Spec.Ctr.aesApi.artifact Arm.target {
    code := Impl.AesCtr.Arm.crypt
    stack := 8
    verified := crypt_verified }]

end VG.Artifacts.AesCtr.Arm
