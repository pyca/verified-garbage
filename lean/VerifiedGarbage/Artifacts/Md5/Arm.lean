import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Md5.Arm.Shared

/-! # MD5 (RFC 1321) on ARMv7 -/

namespace VG.Artifacts.Md5.Arm

def artifacts : List Artifact := [
  { Spec.Md5.compressApi with
    target := Arm.target
    doc := Spec.Md5.compressApi.doc
    code := Impl.Md5.Arm.compress
    contract := Spec.Md5.compressContract Arm.abi
    verified := Proof.Md5.Arm.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Md5.initApi with
    target := Arm.target
    doc := Spec.Md5.initApi.doc
    code := Impl.Md5.Arm.Stream.init
    contract := Spec.Md5.initContract Arm.abi
    verified := Proof.Md5.Arm.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Md5.updateApi with
    target := Arm.target
    doc := Spec.Md5.updateApi.doc
    code := Impl.StackScratch.Arm.withStackScratch 128 2 Impl.Md5.Arm.Stream.update
    contract := Spec.Md5.updateContract Arm.abi 128
    stack := 128
    verified := Proof.Md5.Arm.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Md5.finalizeApi with
    target := Arm.target
    doc := Spec.Md5.finalizeApi.doc
    code := Impl.StackScratch.Arm.withStackScratch 128 1 Impl.Md5.Arm.Stream.finalize
    contract := Spec.Md5.finalizeContract Arm.abi 128
    stack := 128
    verified := Proof.Md5.Arm.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Md5.updateScratchApi with
    target := Arm.target
    doc := Spec.Md5.updateScratchApi.doc
    code := Impl.Md5.Arm.Stream.update
    contract := Spec.Md5.updateScratchContract Arm.abi
    verified := Proof.Md5.Arm.Shared.updateScratch
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Md5.finalizeScratchApi with
    target := Arm.target
    doc := Spec.Md5.finalizeScratchApi.doc
    code := Impl.Md5.Arm.Stream.finalize
    contract := Spec.Md5.finalizeScratchContract Arm.abi
    verified := Proof.Md5.Arm.Shared.finalizeScratch
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Md5.Arm
