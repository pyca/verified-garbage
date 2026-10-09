import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailVerified

namespace VG.Artifacts.MlDsaResident.AArch64
open VG

def artifacts : List Artifact := [
  { Spec.MlDsa.commitTailApi 768 48 with
    features := ["sha3"]
    target := AArch64.target
    doc := (Spec.MlDsa.commitTailApi 768 48).doc
    code := Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48
    contract := Spec.MlDsa.commitTailContract AArch64.abi 768 48
    verified := Proof.MlDsa.AArch64.Sign.CommitTail.verified65
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.commitTailApi 1024 64 with
    features := ["sha3"]
    target := AArch64.target
    doc := (Spec.MlDsa.commitTailApi 1024 64).doc
    code := Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64
    contract := Spec.MlDsa.commitTailContract AArch64.abi 1024 64
    verified := Proof.MlDsa.AArch64.Sign.CommitTail.verified87
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.rejNTT2Api with
    name := Spec.MlDsa.rejNTT2Api.name ++ "_sha3"
    features := ["sha3"]
    target := AArch64.target
    doc := Spec.MlDsa.rejNTT2Api.doc
    code := Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code
    contract := Spec.MlDsa.rejNTT2Contract AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.ResidentRej.two_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.expandMaskPairApi with
    name := Spec.MlDsa.expandMaskPairApi.name ++ "_sha3"
    features := ["sha3"]
    target := AArch64.target
    doc := Spec.MlDsa.expandMaskPairApi.doc
    code := Impl.MlDsa.AArch64.Optimized.ResidentMask.raw
    contract := Spec.MlDsa.expandMaskPairContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.ResidentMask.pair_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.expandMaskPairApi with
    name := Spec.MlDsa.expandMaskPairApi.name ++ "_n2"
    features := ["sha3"]
    target := AArch64.target
    doc := Spec.MlDsa.expandMaskPairApi.doc
    code := Impl.MlDsa.AArch64.Optimized.ResidentMask.rawWith
      (.block Impl.MlDsa.AArch64.Optimized.KeccakMix.rounds)
    contract := Spec.MlDsa.expandMaskPairContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.ResidentMask.pair_n2_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaResident.AArch64
