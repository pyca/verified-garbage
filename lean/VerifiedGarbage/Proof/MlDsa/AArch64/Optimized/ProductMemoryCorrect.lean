import VerifiedGarbage.Spec.MlDsa.RawInverse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalBankFieldRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalBankFieldFold
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRawFinalSlice
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRawMemoryValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryCorrect
import VerifiedGarbage.Spec.MlDsa.FusedInverse

/-! ## From `RawInverseField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem signedPolyAt_get (m : Mem) (p : Addr) {i : Nat} (hi : i<n) :
    (signedPolyAt m p)[i]! =ofInt (coeffAt m p i).toInt := by
  rw [_root_.getElem!_pos (signedPolyAt m p) i hi]
  simp only [signedPolyAt,Vector.getElem_ofFn]

/-- Caller-facing form of the raw contract: strict bounds and exact field
values, without interpreting a negative coefficient as an unsigned integer. -/
theorem rawPolyIs_iff {m : Mem} {p : Addr} {f : Poly} :
    RawPolyIs m p f ↔ ∀ i<n,
      -(q : Int)<(coeffAt m p i).toInt ∧ (coeffAt m p i).toInt<2*(q : Int) ∧
      ofInt (coeffAt m p i).toInt=f[i]! := by
  constructor
  · rintro ⟨hb,hf⟩ i hi
    exact ⟨(hb i hi).1,(hb i hi).2,by rw [← signedPolyAt_get m p hi,hf]⟩
  · intro h
    refine ⟨fun i hi => ⟨(h i hi).1,(h i hi).2.1⟩,ext_getElem! fun i hi => ?_⟩
    rw [signedPolyAt_get m p hi]
    exact (h i hi).2.2

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `InverseRawBankField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Omitting the final correction retains the exact field result in the
strict signed Barrett interval. -/
theorem rawFinalValues_field (v : Vector (BitVec 128) 8) (w : Poly)
    {u : Nat} (hu : u<8) (hv : BankBound v 268173344) (hf : BankField u v w)
    (i : Fin 8) {e : Nat} (he : e<4) :
    -8380417<(vword (rawFinalValues v)[i.val] e).toInt ∧
      (vword (rawFinalValues v)[i.val] e).toInt<2*8380417 ∧
      ofInt (vword (rawFinalValues v)[i.val] e).toInt=
        (InverseTraversal.run (InverseTraversal.stridedSlice u) w)[4*u+32*i.val+e]! * 16382 := by
  have hp := runValues_final_six 0 6 (by decide) v w hu
    ((stageBound_zero v 268173344).mpr hv) hf
  have hl := foldedStage_field _ _ hu hp.1 hp.2 i he
  rw [rawFinalValues,runValues_split_last]
  refine ⟨hl.1,hl.2.1,?_⟩
  simpa only [← InverseTraversal.run_append,stridedOps_eq hu,
    InverseTraversal.stridedLoc,show 32*i.val+4*u+e=4*u+32*i.val+e by omega,
    show ofInt (16382 : Int)=(16382 : Zq) by decide +kernel] using hl.2.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseRawMemoryField.lean` -/

section

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

end

/-! ## From `ProductMemoryCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Centered Montgomery products and the folded inverse scale cancel exactly,
leaving the ordinary polynomial product required by callers. -/
theorem productRawInverse_field {m : Mem} {p a b : Addr} {f g : Poly}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m b g) :
    RawPolyIs (rawFinalPassMem (productPassMem m p a b 8) p 8) p
      (nttInv (multiplyNTT f g)) := by
  have h := rawFinalPass_field (productPass_field (p := p) hf hg)
  rw [InverseTraversal.traversal_montgomery] at h
  change RawPolyIs _ _ (Representation.inverse true (Representation.product true f g)) at h
  simpa only [Representation.inverse_product] using h

/-- The separately retained canonical fused helper has the same ordinary
field result, with its stronger canonical output promise. -/
theorem productInverse_field {m : Mem} {p a b : Addr} {f g : Poly} {qv : BitVec 128}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m b g) (hq : ∀ e<4, vword qv e=8380417#32) :
    PolyIs (finalPassMem (productPassMem m p a b 8) p qv 8) p
      (nttInv (multiplyNTT f g)) := by
  have h := finalPass_field (productPass_field (p := p) hf hg) hq
  rw [InverseTraversal.traversal_montgomery] at h
  change PolyIs _ _ (Representation.inverse true (Representation.product true f g)) at h
  simpa only [Representation.inverse_product] using h

theorem positiveReduced_is {m : Mem} {p : Addr} (h : PositiveReduced m p) :
    PosPolyIs m p (polyAt m p) := ⟨h,rfl⟩

/-- Direct instantiation from the shared raw helper's input predicates. -/
theorem productRawInverse_contract_field {m : Mem} {p a b : Addr}
    (ha : PositiveReduced m a) (hb : PositiveReduced m b) :
    RawPolyIs (rawFinalPassMem (productPassMem m p a b 8) p 8) p
      (nttInv (multiplyNTT (polyAt m a) (polyAt m b))) :=
  productRawInverse_field (positiveReduced_is ha) (positiveReduced_is hb)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
