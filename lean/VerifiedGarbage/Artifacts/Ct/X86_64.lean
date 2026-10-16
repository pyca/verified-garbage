module

public import VerifiedGarbage.Proof.Ct.X86_64
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ct.X86_64
open VG.X86_64

def artifacts : List Artifact := [
  Spec.Ct.eqApi.artifact target {
    code := Impl.Ct.X86_64.eq
    verified := Proof.Ct.X86_64.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]
end VG.Artifacts.Ct.X86_64
