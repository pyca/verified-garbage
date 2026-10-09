import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductRepresentation

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def dotPoly (f g : Nat → Poly) (count : Nat) : Poly :=
  ((List.range count).map fun j => multiplyNTT (f j) (g j)).foldl add zero

theorem dotPoly_zero (f g : Nat → Poly) : dotPoly f g 0=zero := rfl

theorem dotPoly_succ (f g : Nat → Poly) (count : Nat) :
    dotPoly f g (count+1)=add (dotPoly f g count) (multiplyNTT (f count) (g count)) := by
  simp only [dotPoly,List.range_succ,List.map_append,List.map_cons,List.map_nil,
    List.foldl_append,List.foldl_cons,List.foldl_nil]

/-- The indexed family contract is exactly the existing matrix-row sum. -/
theorem dotPoly_lists (f g : List Poly) {count : Nat} (hf : f.length=count) (hg : g.length=count) :
    dotPoly (fun j => f[j]!) (fun j => g[j]!) count=(List.zipWith multiplyNTT f g).foldl add zero := by
  unfold dotPoly
  congr 1
  apply List.ext_getElem
  · simp [hf,hg]
  · intro i hi hj
    have hif : i<f.length := by simpa [hf] using (show i<count by simpa using hi)
    have hig : i<g.length := by omega
    simp only [List.getElem_map,List.getElem_range,List.getElem_zipWith,
      getElem!_pos f i hif,getElem!_pos g i hig]

theorem dotNat_field (a b : Nat → BitVec 32) (f g : Nat → Poly) (count : Nat)
    {i : Nat} (hi : i<n)
    (ha : ∀j<count,ofInt ((a j).toNat : Int)=(f j)[i]!)
    (hb : ∀j<count,ofInt ((b j).toNat : Int)=(g j)[i]!) :
    ofInt (dotNat a b count : Int)=(dotPoly f g count)[i]! := by
  induction count with
  | zero =>
    change ofInt 0=zero[i]!
    rw [getElem!_eq zero hi]
    simp only [zero,Vector.getElem_replicate]
    rfl
  | succ count ih =>
    rw [dotNat,Int.natCast_add,ofInt_add,Int.natCast_mul,ofInt_mul,
      dotPoly_succ,add_get _ _ hi,mul_get _ _ hi]
    rw [ih (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega)),
      ha count (by omega),hb count (by omega)]

theorem centeredDot_field (a b : Nat → BitVec 32) (f g : Nat → Poly) {count : Nat}
    (hc : count≤7) (ha : ∀j<count,(a j).toNat<3*q) (hb : ∀j<count,(b j).toNat<3*q)
    {i : Nat} (hi : i<n)
    (hf : ∀j<count,ofInt ((a j).toNat : Int)=(f j)[i]!)
    (hg : ∀j<count,ofInt ((b j).toNat : Int)=(g j)[i]!) :
    ofInt (centeredDot a b count).toInt=(Representation.encode true (dotPoly f g count))[i]! := by
  have hs := centeredDot_scaled a b hc ha hb
  rw [dotNat_field a b f g count hi hf hg] at hs
  have heq := congrArg (fun x : Zq => x*montgomeryRInv) hs
  have hinv : ofInt 4294967296*montgomeryRInv=1 := by decide +kernel
  rw [Fin.mul_assoc,hinv,Fin.mul_one] at heq
  change _=(Montgomery.scale montgomeryRInv (dotPoly f g count))[i]!
  rw [Montgomery.scale_get]
  exact heq

end VG.Proof.MlDsa.AArch64.Optimized
