module

public import VerifiedGarbage.Proof.Ct.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ct.Common32
public import VerifiedGarbage.TCB.X86.Print

/-! # Constant-time byte comparison on x86 -/

@[expose] public section

namespace VG.Artifacts.Ct.X86
open VG.X86

def artifacts : List Artifact := [
  Spec.Ct.eqApi.artifact target {
    code := Impl.Ct.X86.eq
    verified := .unscrubbed Proof.Ct.X86.verified }]
end VG.Artifacts.Ct.X86
