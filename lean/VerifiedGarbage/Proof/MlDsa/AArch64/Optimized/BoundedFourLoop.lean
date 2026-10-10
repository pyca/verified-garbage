import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBody
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourTraversal

/-! ## From `BoundedFourLoopState.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64 (Keep)

structure Layout (σ : State) (table p q : Addr) (X : List Byte) : Prop where
 short : X.length≤272
 even : X.length%2=0
 stream : ∀i<X.length,σ.mem (q+BitVec.ofNat 64 i)=X[i]!
 streamApart : (⟨q,X.length+2⟩ : Region).Disjoint (polyR p)
 tableApart : (⟨table,1024⟩ : Region).Disjoint (polyR p)
 read : ∀d,d+2≤X.length→InRegions (σ.rd++σ.wr) (q+BitVec.ofNat 64 d) 4
 tableRead : ∀m<16,InRegions (σ.rd++σ.wr) (table+BitVec.ofNat 64 (64*m)) 16 ∧
      InRegions (σ.rd++σ.wr) (table+BitVec.ofNat 64 (64*m)+32) 8
 write : ∀j,j≤252→InRegions σ.wr (coeffAddr p j) 16

structure LoopInv (σ : State) (η : Nat) (table p q : Addr) (L : List Zq) (X : List Byte)
    (done : Nat) (s : State) : Prop where
 bound : done≤X.length
 even : done%2=0
 consts : Consts η table s
 table : TableAt s.mem table
 keep : Keep bodyRegs σ s
 frame : Frame [polyR p] σ.mem s.mem
 stored : Stored s.mem p (parsed η L X done)
 input : s.gpr .x2=q+BitVec.ofNat 64 done
 output : s.gpr .x3=coeffAddr p (parsed η L X done).length
 remaining : s.gpr .x4=BitVec.ofNat 64 (256-(parsed η L X done).length)
 bytes : s.gpr .x5=BitVec.ofNat 64 (X.length-done)
 guard : s.gpr .x8=if (parsed η L X done).length≤252 then BitVec.ofNat 64 (X.length-done) else 0

theorem LoopInv.stream {σ s : State} {η done : Nat} {table p q : Addr} {L : List Zq} {X : List Byte}
    (h : LoopInv σ η table p q L X done s) (hY : Layout σ table p q X) {i : Nat} (hi : i<X.length) :
    s.mem (q+BitVec.ofNat 64 i)=X[i]! := by
  rw [h.frame.bytes (R := ⟨q,X.length+2⟩) (fun r hr=>by
    rw [List.mem_singleton.mp hr]; exact hY.streamApart) (by change X.length+2≤2^64; have:=hY.short; omega) (by change i<X.length+2; omega)]
  exact hY.stream i hi

theorem LoopInv.values {σ s : State} {η done : Nat} {table p q : Addr} {L : List Zq} {X : List Byte}
    (h : LoopInv σ η table p q L X done s) (hY : Layout σ table p q X) (hd : done+2≤X.length) :
    bodyValues η s=accepted η (nibbles X[done]! X[done+1]!) := by
  unfold bodyValues
  rw [h.input,h.stream hY (by omega)]
  have ha : q+BitVec.ofNat 64 done+1=q+BitVec.ofNat 64 (done+1) := by
    rw [BitVec.add_assoc,BitVec.ofNat_add]; rfl
  rw [ha,h.stream hY (by omega)]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourLoopStep.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

theorem vectorLoopStep_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L : List Zq} {X : List Byte}
    (hY : Layout σ table p q X) (h : LoopInv σ η table p q L X done s)
    (hd : done+2≤X.length) (hL : (parsed η L X done).length≤252) :
    WP isa (.block (vectorBody true η)) s (LoopInv σ η table p q L X (done+2)) := by
  refine WP.mono (vectorBody_ok hη h.consts h.table
    (fun m hm=>by rw [h.keep.rd,h.keep.wr]; exact hY.tableRead m hm)
    (by rw [h.keep.rd,h.keep.wr,h.input]; exact hY.read done hd)
    hL (by omega) h.stored h.output h.remaining h.bytes
    (by rw [h.keep.wr]; exact hY.write _ hL)) fun t ht=>?_
  have hl : parsed η L X (done+2)=parsed η L X done++bodyValues η s := by
    rw [parsed_two hη hd hL,h.values hY hd]
  have hbytes : X.length-(done+2)=(X.length-done)-2:=by omega
  refine ⟨by omega,by have:=h.even; omega,
    h.consts.body ht.keep ht.vectors,
    h.table.frame ht.frame (fun r hr=>by rw [List.mem_singleton.mp hr]; exact hY.tableApart),
    (h.keep.trans ht.keep).mono ?_,h.frame.trans ht.frame,?_,?_,?_,?_,?_,?_⟩
  · intro r hr
    simpa only [List.mem_append,or_self] using hr
  · rw [hl]; exact ht.stored
  · rw [ht.input,h.input,BitVec.add_assoc,BitVec.ofNat_add]
    rfl
  · rw [hl]; exact ht.output
  · rw [hl]; exact ht.remaining
  · rw [hbytes]; exact ht.remainingBytes
  · rw [hl,hbytes]; exact ht.guard

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourLoop.lean` -/

section

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

end
