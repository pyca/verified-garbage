import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sm3.Arm.Shared

/-! # SM3 (GB/T 32905-2016) on ARMv7 -/

namespace VG.Artifacts.Sm3.Arm

def artifacts : List Artifact := [
  { Spec.Sm3.compressApi with
    target := Arm.target
    doc := Spec.Sm3.compressApi.doc
    code := Impl.Sm3.Arm.compress
    contract := Spec.Sm3.compressContract Arm.abi
    verified := Proof.Sm3.Arm.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm3.initApi with
    target := Arm.target
    doc := Spec.Sm3.initApi.doc
    code := Impl.Sm3.Arm.Stream.init
    contract := Spec.Sm3.initContract Arm.abi
    verified := Proof.Sm3.Arm.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm3.updateApi with
    target := Arm.target
    doc := Spec.Sm3.updateApi.doc
    code := Impl.StackScratch.Arm.withStackScratch 168 2 Impl.Sm3.Arm.Stream.update
    contract := Spec.Sm3.updateContract Arm.abi 168
    stack := 168
    verified := Proof.Sm3.Arm.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm3.finalizeApi with
    target := Arm.target
    doc := Spec.Sm3.finalizeApi.doc
    code := Impl.StackScratch.Arm.withStackScratch 168 1 Impl.Sm3.Arm.Stream.finalize
    contract := Spec.Sm3.finalizeContract Arm.abi 168
    stack := 168
    verified := Proof.Sm3.Arm.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sm3.Arm
