module

public import VerifiedGarbage.Impl.Ct.X86_64.Fn
public import VerifiedGarbage.Proof.Ct.X86_64
public import VerifiedGarbage.Proof.Ct.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Constant-time byte comparison on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Ct.X86_64
open VG.X86_64

def artifacts : List Artifact := [
  Spec.Ct.eqApi.artifact target { code := Impl.Ct.X86_64.Fn.eq, verified := .scrubbed Proof.Ct.X86_64.eq_scrubbed, spSafe := Proof.Ct.X86_64.eq_spSafe }]
end VG.Artifacts.Ct.X86_64
