import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedProductBankField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryField

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
