import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRawMemoryValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRawBankField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RawInverseField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Every signed final coefficient comes from its independent strided slice;
folded scaling preserves the ordinary field value and the strict raw range. -/
theorem rawFinalPass_field {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-268173344) 268173344) :
    RawPolyIs (rawFinalPassMem m p 8) p
      ((InverseTraversal.run InverseTraversal.stridedSchedule w).map (· * 16382)) := by
  have bank (u : Nat) (hu : u<8) := fun (i : Fin 8) (e : Nat) (he : e<4) =>
    rawFinalValues_field (readBank m (coeffAddr p (4*u)) 128) w hu
      (fun j e he => by
        rw [readBank_coeff m p (4*u) 32 j he]
        exact h.bound _ (by change 4*u+32*j.val+e<256; omega))
      (fun j e he => by
        rw [readBank_coeff m p (4*u) 32 j he]
        simpa only [Traversal.loc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
          h.value (4*u+32*j.val+e) (by change 4*u+32*j.val+e<256; omega)) i he
  apply rawPolyIs_iff.mpr
  intro k hk
  have hi : k/32<8 := by change k<256 at hk; omega
  have hu : k%32/4<8 := by omega
  have he : k%4<4 := by omega
  rw [rawFinalPass_all_values m p hk,getElem!_pos _ (k/32) hi]
  have hh := bank _ hu ⟨k/32,hi⟩ _ he
  refine ⟨hh.1,hh.2.1,?_⟩
  have hidx : 4*(k%32/4)+32*(k/32)+k%4=k := by omega
  rw [hidx] at hh
  rw [map_mul_get _ _ hk,InverseTraversal.strided_coordinate w hk]
  exact hh.2.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
