import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryBankField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem local_coordinate (w : Poly) {k : Nat} (hk : k<n) :
    (InverseTraversal.run InverseTraversal.localSchedule w)[k]! =
      (InverseTraversal.run (InverseTraversal.localSlice (k/32)) w)[k]! := by
  exact InverseTraversal.prefix_selected InverseTraversal.localSlice (fun k => k/32) 8
    (fun u hu => InverseTraversal.local_supported ⟨u,hu⟩) w hk (by change k<256 at hk; omega)

/-- Multiplication is fused into each local block's initial loads. The first
pass therefore needs neither a materialized product polynomial nor an
initialized destination. -/
theorem productPass_field {m : Mem} {p a b : Addr} {f g : Poly}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m b g) :
    SignedPolyIs (productPassMem m p a b 8) p
      (InverseTraversal.run InverseTraversal.localSchedule (Representation.product true f g))
      (-268173344) 268173344 := by
  have bank (u : Nat) (hu : u<8) := fiveValues_field (productValues m a b u)
    (Representation.product true f g) hu (productValues_bound hf hg hu) (productValues_field hf hg hu)
  have lane (k : Nat) (hk : k<n) :
      -268173344≤(coeffAt (productPassMem m p a b 8) p k).toInt ∧
      (coeffAt (productPassMem m p a b 8) p k).toInt≤268173344 ∧
      ofInt (coeffAt (productPassMem m p a b 8) p k).toInt=
        (InverseTraversal.run InverseTraversal.localSchedule (Representation.product true f g))[k]! := by
    have hu : k/32<8 := by change k<256 at hk; omega
    have hi : k%32/4<8 := by omega
    have he : k%4<4 := by omega
    have hb := (bank _ hu).1 ⟨k%32/4,hi⟩ (k%4) he
    have hv := (bank _ hu).2 ⟨k%32/4,hi⟩ (k%4) he
    rw [productPass_all_values m p a b hk,getElem!_pos _ (k%32/4) hi]
    refine ⟨hb.1,hb.2,?_⟩
    have hidx : 32*(k/32)+4*(k%32/4)+k%4=k := by omega
    simpa only [local_coordinate _ hk,Traversal.innerLoc,hidx] using hv
  exact ⟨fun k hk => ⟨(lane k hk).1,(lane k hk).2.1⟩,fun k hk => (lane k hk).2.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
