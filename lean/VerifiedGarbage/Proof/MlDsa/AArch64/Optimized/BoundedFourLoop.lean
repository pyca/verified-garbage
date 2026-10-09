import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourLoopStep

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64 (eval_nonzero eval_zero ne_zero_iff eq_zero_iff)
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

def VectorDone (σ : State) (η : Nat) (table p q : Addr) (L : List Zq) (X : List Byte)
    (s : State) : Prop := ∃done,LoopInv σ η table p q L X done s ∧
      (done=X.length ∨ 252<(parsed η L X done).length)

theorem loopGuard_eval {σ s : State} {η done : Nat} {table p q : Addr}
    {L : List Zq} {X : List Byte} (hY : Layout σ table p q X)
    (h : LoopInv σ η table p q L X done s) :
    isa.eval (.nonzero .x .x8) s=
      some (decide (done<X.length ∧ (parsed η L X done).length≤252)) := by
  rw [eval_nonzero,h.guard]
  by_cases hl : (parsed η L X done).length≤252
  · rw [ite_eq_left hl,ne_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have:=hY.short; omega)]
    congr 1
    apply decide_eq_decide.mpr
    have:=h.bound
    omega
  · rw [ite_eq_right hl]
    simp only [hl,and_false,decide_false]
    rfl

theorem vectorLoop_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L : List Zq} {X : List Byte}
    (hY : Layout σ table p q X) (h : LoopInv σ η table p q L X done s)
    (hd : done<X.length) (hl : (parsed η L X done).length≤252) :
    WP isa (.loop (.block (vectorBody true η)) (.nonzero .x .x8)) s
      (VectorDone σ η table p q L X) := by
  refine WP.loop (M := isa)
    (fun rank s=>∃d,rank=X.length-d ∧ LoopInv σ η table p q L X d s ∧
      d<X.length ∧ (parsed η L X d).length≤252) ?_ (X.length-done) s
      ⟨done,rfl,h,hd,hl⟩
  rintro rank u ⟨d,rfl,hu,hd,hl⟩
  have hd2 : d+2≤X.length:=by have:=hY.even; have:=hu.even; omega
  refine WP.mono (vectorLoopStep_ok hη hY hu hd2 hl) fun v hv=>?_
  have he:=loopGuard_eval hY hv
  by_cases hc : d+2<X.length ∧ (parsed η L X (d+2)).length≤252
  · exact .inr ⟨by rw [he,decide_eq_true hc],X.length-(d+2),by omega,
      d+2,rfl,hv,hc⟩
  · refine .inl ⟨by rw [he,decide_eq_false hc],d+2,hv,?_⟩
    omega

theorem loopGuard_zero {σ s : State} {η done : Nat} {table p q : Addr}
    {L : List Zq} {X : List Byte} (hY : Layout σ table p q X)
    (h : LoopInv σ η table p q L X done s) :
    isa.eval (.zero .x .x8) s=
      some (decide (done=X.length ∨ 252<(parsed η L X done).length)) := by
  rw [eval_zero,h.guard]
  by_cases hl : (parsed η L X done).length≤252
  · rw [ite_eq_left hl,eq_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have:=hY.short; omega)]
    congr 1
    apply decide_eq_decide.mpr
    have:=h.bound
    omega
  · rw [ite_eq_right hl]
    have hn : 252<(parsed η L X done).length:=by omega
    simp only [hn,or_true,decide_true]
    rfl

theorem vectorPhase_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L : List Zq} {X : List Byte}
    (hY : Layout σ table p q X) (h : LoopInv σ η table p q L X done s) :
    WP isa (.ite (.zero .x .x8) (.block [])
      (.loop (.block (vectorBody true η)) (.nonzero .x .x8))) s
      (VectorDone σ η table p q L X) := by
  have hz:=loopGuard_zero hY h
  by_cases he : done=X.length ∨ 252<(parsed η L X done).length
  · exact WP.ite true (by rw [hz,decide_eq_true he])
      (fun _=>WP.block_nil_iff.mpr ⟨done,h,he⟩) (fun h=>nomatch h)
  · exact WP.ite false (by rw [hz,decide_eq_false he]) (fun h=>nomatch h)
      (fun _=>vectorLoop_ok hη hY h (by have:=h.bound; omega) (by omega))

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
