module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ct.Contract
import VerifiedGarbage.Impl.Ct.X86_64.Fn
import VerifiedGarbage.Proof.Ct.X86_64
import VerifiedGarbage.Proof.Ct.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Constant-time byte comparison on x86-64 -/

namespace VG.Artifacts.Ct.X86_64
open VG.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Ct.eqApi.artifact target { code := Impl.Ct.X86_64.Fn.eq, verified := Proof.Ct.X86_64.eq_scrubbed, spSafe := Proof.Ct.X86_64.eq_spSafe }]

spec_apis artifacts

end VG.Artifacts.Ct.X86_64
