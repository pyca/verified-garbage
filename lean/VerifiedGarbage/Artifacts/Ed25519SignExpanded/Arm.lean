module

public import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Expanded
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Ed25519 signing from the seed's cached SHA-512 digest -/

@[expose] public section

namespace VG.Artifacts.Ed25519SignExpanded.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.signExpandedApi.artifact Arm.target {
    code := Impl.Ed25519.Arm.SignCached.codeExpanded
    stack := 280
    verified := Proof.Ed25519.Arm.SignCached.signExpanded_verified }]

end VG.Artifacts.Ed25519SignExpanded.Arm
