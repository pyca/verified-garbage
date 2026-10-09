import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryFinalValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Canonical bank outputs with folded scaling establish the complete final
memory pass's field result, independently of the order of disjoint slices. -/
theorem finalPass_field_of_banks {m : Mem} {p : Addr} {qv : BitVec 128} {w : Poly}
    (hb : ∀ u<8, ∀ i : Fin 8, ∀ e<4,
      (vword (finalValues (readBank m (coeffAddr p (4*u)) 128) qv)[i.val] e).toNat<q)
    (hv : ∀ u<8, ∀ i : Fin 8, ∀ e<4,
      ofInt (vword (finalValues (readBank m (coeffAddr p (4*u)) 128) qv)[i.val] e).toInt=
        (InverseTraversal.run (InverseTraversal.stridedSlice u) w)[4*u+32*i.val+e]! * 16382) :
    PolyIs (finalPassMem m p qv 8) p ((InverseTraversal.run InverseTraversal.stridedSchedule w).map (· * 16382)) := by
  have hout (k : Nat) (hk : k<n) :
      (coeffAt (finalPassMem m p qv 8) p k).toNat<q ∧
      ofInt (coeffAt (finalPassMem m p qv 8) p k).toInt=
        (InverseTraversal.run InverseTraversal.stridedSchedule w)[k]! * 16382 := by
    have hi : k/32<8 := by change k<256 at hk; omega
    have hu : k%32/4<8 := by omega
    have he : k%4<4 := by omega
    rw [finalPass_all_values m p qv hk,getElem!_pos (finalValues (readBank m (coeffAddr p (4*(k%32/4))) 128) qv) (k/32) hi]
    refine ⟨hb _ hu ⟨k/32,hi⟩ _ he,?_⟩
    have hh := hv _ hu ⟨k/32,hi⟩ _ he
    have hidx : 4*(k%32/4)+32*(k/32)+k%4=k := by omega
    rw [hidx] at hh
    rw [InverseTraversal.strided_coordinate w hk]
    exact hh
  refine ⟨fun k hk => (hout k hk).1,ext_getElem! fun k hk => ?_⟩
  rw [polyAt_get _ _ hk,map_mul_get _ _ hk]
  have hh := hout k hk
  have hint : (coeffAt (finalPassMem m p qv 8) p k).toInt=
      ((coeffAt (finalPassMem m p qv 8) p k).toNat : Int) := by
    apply BitVec.toInt_eq_toNat_of_lt
    have hq : q=8380417 := rfl
    omega
  rw [hint,ofInt_nat_eq] at hh
  exact hh.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
