module

public import VerifiedGarbage.Proof.Ffdh.X86_64
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitVerified

@[expose] public section

namespace VG.Artifacts.Ffdh.X86_64
open VG.X86_64

def artifacts : List Artifact := [
  { Spec.Ffdh.chooseApi with
    target := target
    doc := Spec.Ffdh.chooseApi.doc
    code := Impl.Ffdh.X86_64.choose
    contract := Spec.Ffdh.chooseContract abi
    verified := Proof.Ffdh.X86_64.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Ffdh.parameterInitApi with
    target := target
    doc := Spec.Ffdh.parameterInitApi.doc
    code := Impl.Ffdh.X86_64.Generation.init
    contract := Spec.Ffdh.parameterInitContract abi
    verified := by exact Proof.Ffdh.X86_64.Generation.init_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]
end VG.Artifacts.Ffdh.X86_64
