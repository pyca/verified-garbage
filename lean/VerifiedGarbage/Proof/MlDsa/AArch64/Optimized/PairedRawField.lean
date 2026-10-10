import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedProductField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryBankField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryCorrect

/-! ## From `PairedProductBankField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Each paired input bank is exactly the previously verified product bank. -/
theorem valuesAt_productValues (m : Mem) (a b : Addr) (u : Nat) (poly : Fin 2) :
    valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly =
      Inverse.productValues m a (b+BitVec.ofNat 64 (1024*poly.val)) u := by
  apply Vector.ext
  intro j hj
  apply vec_ext
  intro e he
  exact (valuesAt_coeff m a b u poly ⟨j,hj⟩ he).trans
    (Inverse.productValues_word m a (b+BitVec.ofNat 64 (1024*poly.val)) u ⟨j,hj⟩ he).symm

/-- The paired five-layer transform preserves the exact field meaning and
its signed 32q bound for either polynomial. -/
theorem fiveValues_field {m : Mem} {a b : Addr} {u : Nat} {poly : Fin 2} {f g : Poly}
    (hu : u<8) (hf : PosPolyIs m a f)
    (hg : PosPolyIs m (b+BitVec.ofNat 64 (1024*poly.val)) g) :
    BankBound (Inverse.fiveValues u
      (valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly)) 268173344 ∧
    InnerBankField u (Inverse.fiveValues u
      (valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly))
      (InverseTraversal.run (InverseTraversal.localSlice u) (Representation.product true f g)) := by
  rw [valuesAt_productValues]
  exact Inverse.fiveValues_field _ _ hu (Inverse.productValues_bound hf hg hu)
    (Inverse.productValues_field hf hg hu)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedFinalBankField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The strided final-pass bank contains the complete first-five-layer field
result, with the signed range needed by the remaining inverse layers. -/
theorem firstPass_finalBank_field {m : Mem} {p a b : Addr} {u : Nat} (hu : u<8)
    (ha : (⟨a,1024⟩ : Region).Disjoint ⟨p,2048⟩)
    (hb : (⟨b,2048⟩ : Region).Disjoint ⟨p,2048⟩) (poly : Fin 2) {f g : Poly}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m (b+BitVec.ofNat 64 (1024*poly.val)) g) :
    BankBound (readPair (firstPassMem m p a b 8) (p+BitVec.ofNat 64 (16*u)) 128 poly) 268173344 ∧
    ∀j : Fin 8, ∀e<4,
      ofInt (vword ((readPair (firstPassMem m p a b 8) (p+BitVec.ofNat 64 (16*u)) 128 poly)[j.val]) e).toInt =
      (InverseTraversal.run InverseTraversal.localSchedule (Representation.product true f g))[32*j.val+4*u+e]! := by
  rw [firstPass_finalBank hu ha hb poly]
  constructor
  · intro j e he
    simp only [Vector.getElem_ofFn]
    exact (fiveValues_field j.isLt hf hg).1 ⟨u,hu⟩ e he
  · intro j e he
    simp only [Vector.getElem_ofFn]
    have hv := (fiveValues_field j.isLt hf hg).2 ⟨u,hu⟩ e he
    have hi : 32*j.val+4*u+e<n := by change 32*j.val+4*u+e<256; omega
    rw [Inverse.local_coordinate _ hi]
    have hd : (32*j.val+4*u+e)/32=j.val := by omega
    rw [hd]
    exact hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedRawField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The complete paired transform yields the ordinary inverse pointwise
product in the strict signed interval expected by the fused checks. -/
theorem rawFinal_field {m : Mem} {p a b : Addr} {u : Nat} (hu : u<8)
    (ha : (⟨a,1024⟩ : Region).Disjoint ⟨p,2048⟩)
    (hb : (⟨b,2048⟩ : Region).Disjoint ⟨p,2048⟩) (poly : Fin 2) {f g : Poly}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m (b+BitVec.ofNat 64 (1024*poly.val)) g)
    (i : Fin 8) {e : Nat} (he : e<4) :
    let v := Inverse.rawFinalValues (readPair (firstPassMem m p a b 8) (p+BitVec.ofNat 64 (16*u)) 128 poly);
    -8380417<(vword v[i.val] e).toInt ∧ (vword v[i.val] e).toInt<2*8380417 ∧
      ofInt (vword v[i.val] e).toInt=(nttInv (multiplyNTT f g))[4*u+32*i.val+e]! := by
  dsimp only
  have hbank := firstPass_finalBank_field hu ha hb poly hf hg
  have hv := Inverse.rawFinalValues_field _
    (InverseTraversal.run InverseTraversal.localSchedule (Representation.product true f g)) hu hbank.1
    (fun j e he => by simpa only [Traversal.loc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hbank.2 j e he) i he
  refine ⟨hv.1,hv.2.1,hv.2.2.trans ?_⟩
  have hk : 4*u+32*i.val+e<n := by change 4*u+32*i.val+e<256; omega
  have hu' : (4*u+32*i.val+e)%32/4=u := by omega
  have hcoord := InverseTraversal.strided_coordinate
    (InverseTraversal.run InverseTraversal.localSchedule (Representation.product true f g)) hk
  rw [hu'] at hcoord
  rw [←hcoord,←map_mul_get _ _ hk,InverseTraversal.traversal_montgomery]
  change (Representation.inverse true (Representation.product true f g))[_]! = _
  rw [Representation.inverse_product]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
