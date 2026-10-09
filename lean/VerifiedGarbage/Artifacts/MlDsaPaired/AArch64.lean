import VerifiedGarbage.Spec.MlDsa.PairedApi
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowVerified

namespace VG.Artifacts.MlDsaPaired.AArch64

def artifacts : List Artifact := [
  { Spec.MlDsa.pairedZApi with
    target := AArch64.target
    doc := Spec.MlDsa.pairedZApi.doc
    consts := Impl.MlDsa.AArch64.Optimized.Paired.pairedConsts
    code := Impl.MlDsa.AArch64.Optimized.Paired.selected .z
    contract := Spec.MlDsa.pairedZContract
      (AArch64.abi.withConsts Impl.MlDsa.AArch64.Optimized.Paired.pairedConsts)
    verified := Proof.MlDsa.AArch64.Optimized.Paired.pairedZ_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    ofSig := ⟨_,_,_,by unfold Spec.MlDsa.pairedZContract; rfl⟩ },
  { Spec.MlDsa.pairedLowApi with
    target := AArch64.target
    doc := Spec.MlDsa.pairedLowApi.doc
    consts := Impl.MlDsa.AArch64.Optimized.Paired.pairedConsts
    code := Impl.MlDsa.AArch64.Optimized.Paired.selected .r0
    contract := Spec.MlDsa.pairedLowContract
      (AArch64.abi.withConsts Impl.MlDsa.AArch64.Optimized.Paired.pairedConsts)
    verified := Proof.MlDsa.AArch64.Optimized.Paired.pairedLow_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    ofSig := ⟨_,_,_,by unfold Spec.MlDsa.pairedLowContract; rfl⟩ },
  { Spec.MlDsa.pairedHintApi with
    target := AArch64.target
    doc := Spec.MlDsa.pairedHintApi.doc
    consts := Impl.MlDsa.AArch64.Optimized.Paired.pairedConsts
    code := Impl.MlDsa.AArch64.Optimized.Paired.selected .h
    contract := Spec.MlDsa.pairedHintContract
      (AArch64.abi.withConsts Impl.MlDsa.AArch64.Optimized.Paired.pairedConsts)
    verified := Proof.MlDsa.AArch64.Optimized.Paired.pairedHint_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    ofSig := ⟨_,_,_,by unfold Spec.MlDsa.pairedHintContract; rfl⟩ }]

end VG.Artifacts.MlDsaPaired.AArch64
