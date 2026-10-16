module

public import VerifiedGarbage.Proof.Ffdh.X86_64
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ffdh.X86_64
open VG.X86_64

def artifacts : List Artifact := [
  Spec.Ffdh.chooseApi.artifact target {
    code := Impl.Ffdh.X86_64.choose
    verified := Proof.Ffdh.X86_64.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]
end VG.Artifacts.Ffdh.X86_64
