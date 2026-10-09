import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVerified
import VerifiedGarbage.TCB.AArch64.Target

namespace VG.Artifacts.MlDsaDot.AArch64

private def dotArtifact (count : Nat) (hc : count=4 ∨ count=5 ∨ count=7) : Artifact :=
  { Spec.MlDsa.dotInverseApi count with
    target := AArch64.target
    doc := (Spec.MlDsa.dotInverseApi count).doc
    consts := Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts
    code := Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode count
    contract := Spec.MlDsa.dotInverseContract count
      (AArch64.abi.withConsts Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts)
    verified := Proof.MlDsa.AArch64.Optimized.Inverse.dot_verified hc
    spSafe := Code.all_of_forall (fun _ => rfl) _ }

def artifacts : List Artifact := [dotArtifact 4 (by simp),dotArtifact 5 (by simp),dotArtifact 7 (by simp)]

end VG.Artifacts.MlDsaDot.AArch64
