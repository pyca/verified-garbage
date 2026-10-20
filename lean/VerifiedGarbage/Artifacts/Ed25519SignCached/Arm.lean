module

public import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Verified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519SignCached.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.signCachedApi.artifact Arm.target {
    notes := ["Includes SHA-512, scalar reduction, \
      base-point multiplication, and scalar multiply-add. Secret intermediate buffers are cleared before returning."]
    code := Impl.Ed25519.Arm.SignCached.code
    stack := 280
    verified := Proof.Ed25519.Arm.SignCached.signCached_verified }]

end VG.Artifacts.Ed25519SignCached.Arm
