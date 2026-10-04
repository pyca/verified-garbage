import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sha1.Arm.Shared

/-! # SHA-1 (FIPS 180-4) on ARMv7 -/

namespace VG.Artifacts.Sha1.Arm

def artifacts : List Artifact := [
  { Spec.Sha1.compressApi with
    target := Arm.target
    doc := Spec.Sha1.compressApi.doc
    code := Impl.Sha1.Arm.compress
    contract := Spec.Sha1.compressContract Arm.abi
    verified := Proof.Sha1.Arm.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha1.initApi with
    target := Arm.target
    doc := Spec.Sha1.initApi.doc
    code := Impl.Sha1.Arm.Stream.init
    contract := Spec.Sha1.initContract Arm.abi
    verified := Proof.Sha1.Arm.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha1.updateApi with
    target := Arm.target
    doc := Spec.Sha1.updateApi.doc
    code := Impl.StackScratch.Arm.withStackScratch 176 2 Impl.Sha1.Arm.Stream.update
    contract := Spec.Sha1.updateContract Arm.abi 176
    stack := 176
    verified := Proof.Sha1.Arm.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha1.finalizeApi with
    target := Arm.target
    doc := Spec.Sha1.finalizeApi.doc
    code := Impl.StackScratch.Arm.withStackScratch 176 1 Impl.Sha1.Arm.Stream.finalize
    contract := Spec.Sha1.finalizeContract Arm.abi 176
    stack := 176
    verified := Proof.Sha1.Arm.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha1.updateScratchApi with
    target := Arm.target
    doc := Spec.Sha1.updateScratchApi.doc
    code := Impl.Sha1.Arm.Stream.update
    contract := Spec.Sha1.updateScratchContract Arm.abi
    verified := Proof.Sha1.Arm.Shared.updateScratch
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha1.finalizeScratchApi with
    target := Arm.target
    doc := Spec.Sha1.finalizeScratchApi.doc
    code := Impl.Sha1.Arm.Stream.finalize
    contract := Spec.Sha1.finalizeScratchContract Arm.abi
    verified := Proof.Sha1.Arm.Shared.finalizeScratch
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha1.Arm
