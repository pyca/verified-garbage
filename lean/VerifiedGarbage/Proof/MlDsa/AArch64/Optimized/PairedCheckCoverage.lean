import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCoordinates
import VerifiedGarbage.Proof.MlDsa.Sign.Iter

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.Spec.MlDsa

theorem checkCoverage (P : Nat → Nat → Prop) :
    (∀e<4,∀u<8,∀i:Fin 2 × Fin 8,P i.1.val (4*u+32*i.2.val+e)) ↔
      ∀j<2,∀k<n,P j k := by
  constructor
  · intro hall j hj k hk
    obtain ⟨heq,hu,hi,he⟩ := paired_coordinate hk
    have h := hall _ he _ hu (⟨j,hj⟩,⟨k/32,hi⟩)
    simpa only [←heq] using h
  · intro hall e he u hu i
    exact hall i.1.val i.1.isLt _ (by change 4*u+32*i.2.val+e<256; omega)

theorem paired_norm_iff (f : Nat → Poly) {B : Nat} (hB : 0<B) :
    normRq ((List.range 2).map f)<B ↔ ∀j<2,∀k<n,normZq (f j)[k]!<B := by
  rw [VG.Proof.MlDsa.Sign.normRq_lt_iff _ hB]
  simp only [List.forall_mem_map,List.mem_range]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro _
  exact VG.Proof.MlDsa.Round.normRq_lt _ _

end VG.Proof.MlDsa.AArch64.Optimized.Paired
