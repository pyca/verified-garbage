import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified

namespace VG.Artifacts.MlDsaVerifyHelpers.AArch64

def artifacts : List Artifact := [
  { Spec.MlDsa.subApi with
    name := "vg_mldsa_verify_sub"
    target := AArch64.target
    doc := Spec.MlDsa.subApi.doc
    code := Impl.MlDsa.AArch64.Optimized.AddSub.code true
    contract := Spec.MlDsa.subContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.AddSub.sub_verified
    spSafe := Code.all_of_forall (fun _=>rfl) _ }]

end VG.Artifacts.MlDsaVerifyHelpers.AArch64
