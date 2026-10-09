import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowSpecPre

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem pairPoly_contains (p : Addr) {j : Nat} (hj : j<2) :
    (⟨p,2048⟩ : Region).Contains (pairPolyPtr p j) 1024 :=
  Offset.contains_base p (by omega) (by omega)

theorem positiveReduced_frame {rs : List Region} {m m' : Mem} {p : Addr}
    (hf : Frame rs m m') (hd : ∀r∈rs,(⟨p,1024⟩:Region).Disjoint r)
    (hp : PositiveReduced m p) : PositiveReduced m' p := by
  intro i hi
  rw [VG.Proof.MlDsa.Verify.coeffAt_congr (VG.Proof.MlKem.bytes_frame hf hd (by decide)) hi]
  exact hp i hi

theorem pairedProduct_frame {rs : List Region} {m m' : Mem} {challenge secret : Addr}
    (hf : Frame rs m m')
    (hc : ∀r∈rs,(⟨challenge,1024⟩:Region).Disjoint r)
    (hs : ∀r∈rs,(⟨secret,2048⟩:Region).Disjoint r) {j : Nat} (hj : j<2) :
    pairedProduct m' challenge secret j=pairedProduct m challenge secret j := by
  have hp : ∀r∈rs,(⟨pairPolyPtr secret j,1024⟩:Region).Disjoint r := by
    intro r hr
    exact (hs r hr).sub_left (Offset.sub_base secret (by omega))
  rw [pairedProduct,VG.Proof.MlDsa.Verify.polyAt_frame hf hc,
    VG.Proof.MlDsa.Verify.polyAt_frame hf hp]
  rfl

theorem pairedProductsReduced_frame {rs : List Region} {m m' : Mem} {challenge secret : Addr}
    (hf : Frame rs m m')
    (hc : ∀r∈rs,(⟨challenge,1024⟩:Region).Disjoint r)
    (hs : ∀r∈rs,(⟨secret,2048⟩:Region).Disjoint r)
    (hp : pairedProductsReduced m challenge secret) : pairedProductsReduced m' challenge secret := by
  refine ⟨positiveReduced_frame hf hc hp.1,?_⟩
  intro j hj
  apply positiveReduced_frame hf _ (hp.2 j hj)
  intro r hr
  exact (hs r hr).sub_left (Offset.sub_base secret (by omega))

theorem pairedDifference_frame {rs : List Region} {m m' : Mem} {challenge secret out : Addr}
    (hf : Frame rs m m')
    (hc : ∀r∈rs,(⟨challenge,1024⟩:Region).Disjoint r)
    (hs : ∀r∈rs,(⟨secret,2048⟩:Region).Disjoint r)
    (ho : ∀r∈rs,(⟨out,2048⟩:Region).Disjoint r) {j : Nat} (hj : j<2) :
    pairedDifference m' challenge secret out j=pairedDifference m challenge secret out j := by
  have hp : ∀r∈rs,(⟨pairPolyPtr out j,1024⟩:Region).Disjoint r := by
    intro r hr
    exact (ho r hr).sub_left (Offset.sub_base out (by omega))
  rw [pairedDifference,VG.Proof.MlDsa.Verify.polyAt_frame hf hp,
    pairedProduct_frame hf hc hs hj]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
