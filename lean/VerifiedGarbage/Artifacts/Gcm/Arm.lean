module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Gcm.Arm.Ghash
import Mathlib.Data.List.Induction
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration

/-! # GHASH on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Gcm.Arm

def artifacts : List Artifact := [
  Spec.Gcm.ghashApi.artifact Arm.target {
    notes := ["`•` is computed bit by bit as Algorithm 1 of §6.3 does, with masks instead of \
        branches."]
    code := Impl.Gcm.Arm.ghash
    verified := Proof.Gcm.Arm.ghash_verified }]

end VG.Artifacts.Gcm.Arm
