module

public import VerifiedGarbage.Proof.Ct.AArch64
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ct.AArch64
open VG.AArch64

def artifacts : List Artifact := [
  Spec.Ct.eqApi.artifact target {
    code := Impl.Ct.AArch64.eq
    verified := Proof.Ct.AArch64.verified }]
end VG.Artifacts.Ct.AArch64
