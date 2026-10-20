module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailVerified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.MlDsaResident.AArch64
open VG

def artifacts : List Artifact := [
  (Spec.MlDsa.commitTailApi 768 48).artifact AArch64.target {
    features := ["sha3"]
    code := Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48
    verified := Proof.MlDsa.AArch64.Sign.CommitTail.verified65 },
  (Spec.MlDsa.commitTailApi 1024 64).artifact AArch64.target {
    features := ["sha3"]
    code := Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64
    verified := Proof.MlDsa.AArch64.Sign.CommitTail.verified87 },
  Spec.MlDsa.rejNTT2Api.artifact AArch64.target {
    suffix := "_sha3"
    features := ["sha3"]
    code := Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code
    verified := Proof.MlDsa.AArch64.Optimized.ResidentRej.two_verified },
  Spec.MlDsa.expandMaskPairApi.artifact AArch64.target {
    suffix := "_sha3"
    features := ["sha3"]
    code := Impl.MlDsa.AArch64.Optimized.ResidentMask.raw
    verified := Proof.MlDsa.AArch64.Optimized.ResidentMask.pair_verified }]

end VG.Artifacts.MlDsaResident.AArch64
