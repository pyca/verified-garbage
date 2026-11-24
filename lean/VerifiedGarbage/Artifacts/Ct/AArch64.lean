module

public import VerifiedGarbage.Impl.Ct.AArch64.Fn
public import VerifiedGarbage.Proof.Ct.AArch64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.TCB.AArch64.Target

/-! # Constant-time byte comparison on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Ct.AArch64
open VG.AArch64

def artifacts : List (Artifact AArch64.target) := [
  Spec.Ct.eqApi.artifact target {
    code := Impl.Ct.AArch64.Fn.eq
    verified := Proof.Ct.AArch64.eqCleared_scrubbed }]
end VG.Artifacts.Ct.AArch64
