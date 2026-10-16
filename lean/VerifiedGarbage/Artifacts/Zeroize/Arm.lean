module

public import VerifiedGarbage.Proof.Zeroize.Arm
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Zeroize.Arm
open VG.Arm

def artifacts : List Artifact := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.Arm.zeroize
    verified := Proof.Zeroize.Arm.verified }]
end VG.Artifacts.Zeroize.Arm
