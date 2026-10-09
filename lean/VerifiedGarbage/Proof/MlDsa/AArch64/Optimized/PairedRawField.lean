import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalBankField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryCorrect

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
