module

public import VerifiedGarbage.Proof.Ct.X86
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ct.X86
open VG.X86

def artifacts : List Artifact := [
  Spec.Ct.eqApi.artifact target {
    code := Impl.Ct.X86.eq
    verified := Proof.Ct.X86.verified
    stack := 4 }]
end VG.Artifacts.Ct.X86
