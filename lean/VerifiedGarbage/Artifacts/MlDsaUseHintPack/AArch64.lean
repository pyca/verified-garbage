import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackVerified

namespace VG.Artifacts.MlDsaUseHintPack.AArch64

def artifacts : List Artifact := [
  { Spec.MlDsa.useHintPackApi 261888 with
    target := VG.AArch64.target
    doc := (Spec.MlDsa.useHintPackApi 261888).doc
    code := Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
    contract := Spec.MlDsa.useHintPackContract 261888 VG.AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.UseHintPack.pack_verified (by decide)
    spSafe := Code.all_of_forall (fun _=>rfl) _ },
  { Spec.MlDsa.useHintPackApi 95232 with
    target := VG.AArch64.target
    doc := (Spec.MlDsa.useHintPackApi 95232).doc
    code := Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
    contract := Spec.MlDsa.useHintPackContract 95232 VG.AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.UseHintPack.pack_verified (by decide)
    spSafe := Code.all_of_forall (fun _=>rfl) _ }]

end VG.Artifacts.MlDsaUseHintPack.AArch64
