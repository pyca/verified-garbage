module

public import VerifiedGarbage.Proof.Gcm.Arm.Ghash
public import VerifiedGarbage.Proof.Framework.Registration

/-! # GHASH on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Gcm.Arm

def artifacts : List Artifact := [
  Spec.Gcm.ghashApi.artifact Arm.target {
    code := Impl.Gcm.Arm.ghash
    verified := Proof.Gcm.Arm.ghash_verified }]

end VG.Artifacts.Gcm.Arm
