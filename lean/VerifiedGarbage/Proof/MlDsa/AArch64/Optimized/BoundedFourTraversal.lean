import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMath

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Sample

/-- Meaningful output after a prefix of a sampler stream. -/
def parsed (η : Nat) (L : List Zq) (X : List Byte) (done : Nat) : List Zq :=
 rbFold η L (X.take done)

theorem parsed_zero (η : Nat) (L : List Zq) (X : List Byte) : parsed η L X 0=L := rfl

theorem parsed_bound {η : Nat} {L : List Zq} {X : List Byte} (hL : L.length≤256) (done : Nat) :
    (parsed η L X done).length≤256 := rbFold_length_le hL _

theorem take_two {X : List Byte} {done : Nat} (h : done+2≤X.length) :
    X.take (done+2)=X.take done++[X[done]!,X[done+1]!] := by
  rw [show done+2=(done+1)+1 by omega,List.take_succ_eq_append_getElem (by omega),
    List.take_succ_eq_append_getElem (by omega),List.append_assoc]
  simp only [getElem!_pos X done (by omega),getElem!_pos X (done+1) (by omega)]
  rfl

theorem parsed_two {η : Nat} (hη : η=2∨η=4) {L : List Zq} {X : List Byte} {done : Nat}
    (hd : done+2≤X.length) (hL : (parsed η L X done).length≤252) :
    parsed η L X (done+2)=parsed η L X done++accepted η (nibbles X[done]! X[done+1]!) := by
  rw [parsed,take_two hd,rbFold_append]
  exact twoBytes_values hη hL _ _

theorem parsed_one {η : Nat} {L : List Zq} {X : List Byte} {done : Nat} (hd : done<X.length) :
    parsed η L X (done+1)=rbStep η (parsed η L X done) X[done]! := by
  rw [parsed,List.take_succ_eq_append_getElem hd,rbFold_append,getElem!_pos X done hd]
  rfl

theorem parsed_complete {η : Nat} {L : List Zq} {X : List Byte} {done : Nat}
    (he : done=X.length ∨ (parsed η L X done).length=256) :
    parsed η L X done=rbFold η L X := by
  rcases he with rfl|hfull
  · simp only [parsed,List.take_length]
  · have heq : rbFold η L X=rbFold η (parsed η L X done) (X.drop done) := by
      simp only [parsed]
      rw [←rbFold_append, List.take_append_drop]
    rw [heq,rbFold_full hfull]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
