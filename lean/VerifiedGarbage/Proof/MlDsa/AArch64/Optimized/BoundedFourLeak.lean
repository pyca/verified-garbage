import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSelect
import VerifiedGarbage.Proof.MlDsa.Sample.RejBounded

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Sample

/-- A table index depends on rejection decisions, not accepted coefficient values. -/
theorem accept_decide_congr {η a b : Nat} (hη : η=2∨η=4)
    (h : halfByteOk η a=halfByteOk η b) : decide (a<rbB η)=decide (b<rbB η) := by
  rw [halfByteOk_eq hη,halfByteOk_eq hη] at h
  by_cases ha : a<rbB η <;> by_cases hb : b<rbB η <;> simp_all <;> omega

def bytePairMask (η : Nat) (a b : Byte) : Nat :=
 nibbleMask η (a.toNat%16) (a.toNat/16) (b.toNat%16) (b.toNat/16)

theorem bytePairMask_congr {η : Nat} (hη : η=2∨η=4) {a b c d : Byte}
    (ha : hbOks η a=hbOks η c) (hb : hbOks η b=hbOks η d) :
    bytePairMask η a b=bytePairMask η c d := by
  have ha0:=accept_decide_congr hη (congrArg Prod.fst ha)
  have ha1:=accept_decide_congr hη (congrArg Prod.snd ha)
  have hb0:=accept_decide_congr hη (congrArg Prod.fst hb)
  have hb1:=accept_decide_congr hη (congrArg Prod.snd hb)
  unfold bytePairMask nibbleMask
  rw [ha0,ha1,hb0,hb1]

/-- Equality of the old per-byte transcript determines each vector lookup. -/
theorem transcript_pair {η : Nat} (hη : η=2∨η=4) {X Y : List Byte}
    (h : X.map (hbOks η)=Y.map (hbOks η)) (j : Nat)
    (hx : j+1<X.length) (hy : j+1<Y.length) :
    bytePairMask η X[j]! X[j+1]! =bytePairMask η Y[j]! Y[j+1]! := by
  have hat (i : Nat) (hi : i<X.length) (hj : i<Y.length) :
      hbOks η X[i]! =hbOks η Y[i]! := by
    have hh:=congrArg (fun L : List (Nat×Nat)=>L[i]!) h
    simpa only [getElem!_pos (X.map (hbOks η)) i (by simpa using hi),
      getElem!_pos (Y.map (hbOks η)) i (by simpa using hj),List.getElem_map,
      getElem!_pos X i hi,getElem!_pos Y i hj] using hh
  exact bytePairMask_congr hη (hat j (by omega) (by omega)) (hat (j+1) hx hy)

/-- Both vector and scalar cursors depend only on the original transcript. -/
theorem transcript_prefix_length {η : Nat} {X Y : List Byte} {L M : List Zq}
    (h : X.map (hbOks η)=Y.map (hbOks η)) (hl : L.length=M.length) (j : Nat) :
    (rbFold η L (X.take j)).length=(rbFold η M (Y.take j)).length :=
  rbFold_length_congr hl (by rw [List.map_take,List.map_take,h])

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
