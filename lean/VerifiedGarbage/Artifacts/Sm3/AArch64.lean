import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sm3.AArch64.Shared

/-! # SM3 (GB/T 32905-2016) on AArch64 -/

namespace VG.Artifacts.Sm3.AArch64

def artifacts : List Artifact := [
  { Spec.Sm3.compressApi with
    target := AArch64.target
    doc := Spec.Sm3.compressApi.doc
    code := Impl.Sm3.AArch64.compress
    contract := Spec.Sm3.compressContract AArch64.abi
    verified := Proof.Sm3.AArch64.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm3.initApi with
    target := AArch64.target
    doc := Spec.Sm3.initApi.doc
    code := Impl.Sm3.AArch64.Stream.init
    contract := Spec.Sm3.initContract AArch64.abi
    verified := Proof.Sm3.AArch64.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm3.updateApi with
    target := AArch64.target
    doc := Spec.Sm3.updateApi.doc
    code := Impl.StackScratch.AArch64.withStackScratch 112 .x4 Impl.Sm3.AArch64.Stream.update
    contract := Spec.Sm3.updateContract AArch64.abi (16 + 112)
    stack := 16 + 112
    verified := Proof.Sm3.AArch64.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm3.finalizeApi with
    target := AArch64.target
    doc := Spec.Sm3.finalizeApi.doc
    code := Impl.StackScratch.AArch64.withStackScratch 112 .x3 Impl.Sm3.AArch64.Stream.finalize
    contract := Spec.Sm3.finalizeContract AArch64.abi (16 + 112)
    stack := 16 + 112
    verified := Proof.Sm3.AArch64.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sm3.AArch64
