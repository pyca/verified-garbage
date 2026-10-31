module

public import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Verified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519SignCached.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.signCachedApi.artifact Arm.target {
    consts := Impl.Ed25519.Arm.combConsts
    code := Impl.Ed25519.Arm.SignCached.code
    stack := 280
    verified := Proof.Ed25519.Arm.SignCached.signCached_verified }]

end VG.Artifacts.Ed25519SignCached.Arm
