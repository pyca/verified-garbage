import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified

namespace VG.Artifacts.MlDsaKeygenHelpers.AArch64

def artifacts : List Artifact := [
  { Spec.MlDsa.addApi with
    name := "vg_mldsa_keygen_add"
    target := AArch64.target
    doc := Spec.MlDsa.addApi.doc
    code := Impl.MlDsa.AArch64.Optimized.AddSub.code false
    contract := Spec.MlDsa.addContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.AddSub.add_verified
    spSafe := Code.all_of_forall (fun _=>rfl) _ },
  { Spec.MlDsa.simpleBitPackApi with
    name := "vg_mldsa_keygen_simple_bit_pack"
    target := AArch64.target
    doc := Spec.MlDsa.simpleBitPackApi.doc
    code := Impl.MlDsa.AArch64.Optimized.KeygenPack.simple
    contract := Spec.MlDsa.simpleBitPackContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.KeygenPack.simple_verified
    spSafe := Code.all_of_forall (fun _=>rfl) _ },
  { Spec.MlDsa.bitPackApi with
    name := "vg_mldsa_keygen_bit_pack"
    target := AArch64.target
    doc := Spec.MlDsa.bitPackApi.doc
    code := Impl.MlDsa.AArch64.Optimized.KeygenPack.signed
    contract := Spec.MlDsa.bitPackContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.KeygenPack.signed_verified
    spSafe := Code.all_of_forall (fun _=>rfl) _ },
  { Spec.MlDsa.power2RoundApi with
    name := "vg_mldsa_keygen_power2round"
    target := AArch64.target
    doc := Spec.MlDsa.power2RoundApi.doc
    code := Impl.MlDsa.AArch64.Optimized.KeygenRound.power2Round
    contract := Spec.MlDsa.power2RoundContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.KeygenRound.power2Round_verified
    spSafe := Code.all_of_forall (fun _=>rfl) _ }]

end VG.Artifacts.MlDsaKeygenHelpers.AArch64
