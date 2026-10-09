import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailInsert

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def clearPrefix (B : Spec.Sha3.State) (n : Nat) : Spec.Sha3.State :=
  Vector.ofFn fun i => if 8≤i.val ∧ i.val<8+n then 0 else B[i]

theorem clearPrefix_get (B : Spec.Sha3.State) (n i : Nat) (hi : i<25) :
    (clearPrefix B n)[i]! = if 8≤i ∧ i<8+n then 0 else B[i]! := by
  rw [VG.Proof.Sha3.getElem!_eq _ hi,VG.Proof.Sha3.getElem!_eq B hi]
  simp only [clearPrefix,Vector.getElem_ofFn,Fin.getElem_fin]

theorem clearPrefix_step (B : Spec.Sha3.State) (j : Nat) :
    replaceWord (clearPrefix B j) (8+j) 0=clearPrefix B (j+1) := by
  apply Vector.ext
  intro i hi
  rw [← VG.Proof.Sha3.getElem!_eq _ hi,← VG.Proof.Sha3.getElem!_eq _ hi,
    replaceWord_get _ _ _ _ hi,clearPrefix_get _ _ _ hi,clearPrefix_get _ _ _ hi]
  by_cases he : i=8+j
  · subst i
    rw [ite_eq_left rfl,ite_eq_left (by omega)]
  · have hc : (8≤i ∧ i<8+j)↔(8≤i ∧ i<8+(j+1)) := by omega
    simp only [he,ite_false,hc]

/-- Clears the unused second-lane seed words, preserving the first stream. -/
theorem clearHigh_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B)
    (h7 : s.gpr .x7=0) :
    WP isa (.block ((List.range 17).map fun j => .vop (.ins .d2 (vreg (8+j)) 1 .x7))) s fun t =>
      RegKeep [] s t ∧ t.mem=s.mem ∧ Pairs t A (clearPrefix B 17) := by
  let I := fun j t => RegKeep [] s t ∧ t.mem=s.mem ∧ Pairs t A (clearPrefix B j)
  have hz : clearPrefix B 0=B := by
    apply Vector.ext
    intro i hi
    simp only [clearPrefix,Vector.getElem_ofFn,Fin.getElem_fin,Nat.add_zero]
    rw [ite_eq_right (by omega)]
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa) I (fun j t hj ht => ?_) 17 (Nat.le_refl _) s ?_
  · rcases ht with ⟨hk,hm,hp⟩
    refine WP.mono (insertHigh_ok (by omega) hp) fun u ⟨hk',hm',hp'⟩ => ?_
    refine ⟨(hk.trans hk').mono (by simp),hm'.trans hm,?_⟩
    rw [hk.gpr .x7 (by simp),h7,clearPrefix_step] at hp'
    exact hp'
  · exact ⟨RegKeep.refl _ _,rfl,by rw [hz]; exact hp⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
