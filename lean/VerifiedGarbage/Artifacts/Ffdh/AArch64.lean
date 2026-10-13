module

public import VerifiedGarbage.Proof.Ffdh.AArch64
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section

namespace VG.Artifacts.Ffdh.AArch64
open VG.AArch64

def artifacts : List Artifact := [
  { Spec.Ffdh.chooseApi with
    target := target
    doc := Spec.Ffdh.chooseApi.doc
    code := Impl.Ffdh.AArch64.choose
    contract := Spec.Ffdh.chooseContract abi
    verified := Proof.Ffdh.AArch64.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ffdh.AArch64
