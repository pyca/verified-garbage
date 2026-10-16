module

public import VerifiedGarbage.Proof.Ct.Arm
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ct.Arm
open VG.Arm

def artifacts : List Artifact := [
  Spec.Ct.eqApi.artifact target {
    code := Impl.Ct.Arm.eq
    verified := Proof.Ct.Arm.verified
    stack := 4 }]
end VG.Artifacts.Ct.Arm
