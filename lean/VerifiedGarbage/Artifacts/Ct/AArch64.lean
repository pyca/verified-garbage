module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ct.Contract
import VerifiedGarbage.Impl.Ct.AArch64.Fn
import VerifiedGarbage.Proof.Ct.AArch64
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Constant-time byte comparison on AArch64 -/

namespace VG.Artifacts.Ct.AArch64
open VG.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ct.eqApi.artifact target {
    code := Impl.Ct.AArch64.Fn.eq
    verified := Proof.Ct.AArch64.eqCleared_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Ct.AArch64
