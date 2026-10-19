module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchState
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParse
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ## From `BoundedFourBatchStep.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

def updateBatch (η i : Nat) (L : Nat→List Zq) (X : Nat→List Byte) : Nat→List Zq :=
 fun j=>if j=i then rbFold η (L i) (X i) else L j

theorem batchStep_ok {σ s : State} {b p : Addr} {η i off : Nat} (he : η=2∨η=4)
    (hi : i<4) {L : Nat→List Zq} {X : Nat→List Byte}
    (hy : BatchLayout σ b p off X) (hs : BatchInv σ s b p L)
    (h24 : s.gpr .x24=inputAt b i off) (h25 : s.gpr .x25=outputAt p i)
    (h26 : s.gpr .x26=countAt b i) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η) s fun t=>
      BatchInv σ t b p (updateBatch η i L X) ∧
      t.gpr .x24=inputAt b i off+BitVec.ofNat 64 544 ∧
      t.gpr .x25=outputAt p i+BitVec.ofNat 64 1024 ∧
      t.gpr .x26=countAt b i+BitVec.ofNat 64 8 ∧ t.gpr .x27=s.gpr .x27-BitVec.ofNat 64 1 := by
  refine WP.mono (parse_ok he (hs.fields.bound i hi) (hy.length i hi)
    ((hy.vector i hi).frame hs.keep hs.frame (hy.streamsApart i hi))
    ((hy.scalar i hi).frame hs.keep hs.frame (hy.streamsApart i hi))
    hs.table (hs.fields.stored i hi) h24 h25 h26
    (by rw [hs.base]) (hs.fields.count i hi)
    (by rw [hs.keep.rd,hs.keep.wr]; exact hy.countRead i hi)
    (by rw [hs.keep.wr]; exact hy.countWrite i hi) (hy.outputCount i hi i hi))
    fun t ⟨ht,hf,hstore,hcount,t24,t25,t26,t27⟩=>?_
  refine ⟨?_,t24,t25,t26,t27⟩
  have hwide:=parseFrame_batch hi hf
  refine ⟨(hs.keep.trans ht).mono (by decide),hs.frame.trans hwide,?_,?_,
    hs.table.frame hwide hy.tableApart,?_⟩
  · rw [ht.gpr .x19 (by decide)]; exact hs.base
  · rw [ht.gpr .x21 (by decide)]; exact hs.output
  constructor
  · intro j hj
    unfold updateBatch
    split
    · exact rbFold_length_le (hs.fields.bound i hi) _
    · exact hs.fields.bound j hj
  · intro j hj
    by_cases heq : j=i
    · subst j
      simpa only [updateBatch,ite_true] using hstore
    · simp only [updateBatch,heq,ite_false]
      refine stored_frame hf ?_ (hs.fields.stored j hj) (hs.fields.bound j hj)
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact outputs_apart p hj hi heq
      · exact hy.outputCount j hj i hi
  · intro j hj
    by_cases heq : j=i
    · subst j
      simpa only [updateBatch,ite_true] using hcount
    · simp only [updateBatch,heq,ite_false]
      rw [hf.readW (Region.contains_self (countAt b j) 8) (fun r hr=>?_) (by decide)]
      · exact hs.fields.count j hj
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl
        · exact (hy.outputCount i hi j hj).symm
        · exact counts_apart b hj hi heq

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourBatch.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

theorem BatchInv.congr {σ s : State} {b p : Addr} {L L' : Nat→List Zq}
    (h : BatchInv σ s b p L) (he : ∀i<4,L i=L' i) : BatchInv σ s b p L' := by
  refine {h with fields := ⟨?_,?_,?_⟩}
  · intro i hi; rw [←he i hi]; exact h.fields.bound i hi
  · intro i hi; rw [←he i hi]; exact h.fields.stored i hi
  · intro i hi; rw [←he i hi]; exact h.fields.count i hi

/-- The rows after the first `i` streams' parses. -/
def doneBatch (η i : Nat) (L : Nat→List Zq) (X : Nat→List Byte) : Nat→List Zq :=
 fun j=>if j<i then rbFold η (L j) (X j) else L j

/-- The batch loop before stream `i`'s parse. -/
def BatchAt (σ : State) (b p : Addr) (η off : Nat) (L : Nat→List Zq) (X : Nat→List Byte)
    (i : Nat) (s : State) : Prop :=
 BatchInv σ s b p (doneBatch η i L X) ∧ s.gpr .x24=inputAt b i off ∧
   s.gpr .x25=outputAt p i ∧ s.gpr .x26=countAt b i ∧ s.gpr .x27=BitVec.ofNat 64 (4-i)

theorem BatchInv.only {σ s t : State} {b p : Addr} {L : Nat→List Zq} {rs : List Reg}
    (h : BatchInv σ s b p L) (ht : Only rs s t) (hr : ∀r∈rs,r∈batchRegs := by decide) :
    BatchInv σ t b p L :=
  ⟨(h.keep.trans ht.keep).mono (fun r hm=>by
      rcases List.mem_append.mp hm with hm|hm
      · exact hm
      · exact hr r hm),by rw [ht.mem]; exact h.frame,
    by rw [ht.get .x19 (fun hm=>absurd (hr _ hm) (by decide))]; exact h.base,
    by rw [ht.get .x21 (fun hm=>absurd (hr _ hm) (by decide))]; exact h.output,
    by rw [ht.mem]; exact h.table,
    by rw [ht.mem]; exact h.fields⟩

theorem batchAt_init {σ s : State} {b p : Addr} {η off : Nat} (ho : off≤272)
    {L : Nat→List Zq} {X : Nat→List Byte} (hs : BatchInv σ s b p L) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.BoundedFour.batchInit off)) s
      (BatchAt σ b p η off L X 0) := by
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.batchInit
  refine wp_addImm (by omega) fun a ha ea=>wp_mov fun c hc ec=>
    wp_addImm (by decide) fun d hd ed=>wp_addImm (by decide) fun e he ee=>
    wp_movz fun t ht et=>wp_nil ?_
  have hO : Only [.x24,.x25,.x26,.x27] s t :=
    ((((ha.trans hc).trans hd).trans he).trans ht).mono (by decide)
  refine ⟨(hs.only hO).congr fun j _=>by simp [doneBatch],?_,?_,?_,?_⟩
  · rw [ht.get .x24,he.get .x24,hd.get .x24,hc.get .x24,ea,hs.base]
    change _=b+BitVec.ofNat 64 (840+544*0+off)
    exact congrArg (fun d=>b+BitVec.ofNat 64 d) (by omega)
  · rw [ht.get .x25,he.get .x25,hd.get .x25,ec,ha.get .x21,hs.output]
    exact (BitVec.add_zero _).symm
  · rw [ht.get .x26,ee,ed,hc.get .x19,ha.get .x19,hs.base,Offset.add_add]
    change _=b+BitVec.ofNat 64 (7904+8*0)
    exact congrArg (fun d=>b+BitVec.ofNat 64 d)
      (by unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.counts; omega)
  · rw [et]; decide

theorem batchAt_step {σ s : State} {b p : Addr} {η i off : Nat} (he : η=2∨η=4) (hi : i<4)
    {L : Nat→List Zq} {X : Nat→List Byte} (hy : BatchLayout σ b p off X)
    (h : BatchAt σ b p η off L X i s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η) s
      (BatchAt σ b p η off L X (i+1)) := by
  refine WP.mono (batchStep_ok he hi hy h.1 h.2.1 h.2.2.1 h.2.2.2.1)
    fun t ⟨ht,t24,t25,t26,t27⟩=>?_
  refine ⟨ht.congr fun j _=>?_,?_,?_,?_,?_⟩
  · unfold updateBatch doneBatch
    by_cases hj : j=i
    · subst hj; simp
    · by_cases hji : j<i
      · simp [hj,hji,show j<i+1 by omega]
      · simp [hj,hji,show ¬j<i+1 by omega]
  · rw [t24]; unfold inputAt; rw [Offset.add_add]
    exact congrArg (fun d=>b+BitVec.ofNat 64 d) (by omega)
  · rw [t25]; unfold outputAt; rw [Offset.add_add]
    exact congrArg (fun d=>p+BitVec.ofNat 64 d) (by omega)
  · rw [t26]; unfold countAt; rw [Offset.add_add]
    exact congrArg (fun d=>b+BitVec.ofNat 64 d) (by omega)
  · rw [t27,h.2.2.2.2,show 4-i=(4-(i+1))+1 by omega,BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _

private theorem ofNat_bne_zero {k : Nat} (h : k<2^64) :
    (BitVec.ofNat 64 k != 0)=decide (k≠0) := by
  by_cases hk : k=0
  · subst hk; rfl
  · have : BitVec.ofNat 64 k≠0 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    rw [show (BitVec.ofNat 64 k != 0)=true from bne_iff_ne.mpr this]
    simp [hk]

theorem batchAt_eval {σ s : State} {b p : Addr} {η i off : Nat}
    {L : Nat→List Zq} {X : Nat→List Byte} (h : BatchAt σ b p η off L X i s) :
    isa.eval (.nonzero .x .x27) s=some (decide (4-i≠0)) := by
  show some (s.read .x .x27 != 0)=_
  have hrd : s.read .x .x27=s.gpr .x27 := rfl
  rw [hrd,h.2.2.2.2,ofNat_bne_zero (by omega)]

theorem BatchAt.last {σ s : State} {b p : Addr} {η off : Nat}
    {L : Nat→List Zq} {X : Nat→List Byte} (h : BatchAt σ b p η off L X 4 s) :
    BatchInv σ s b p (fun i=>rbFold η (L i) (X i)) :=
  h.1.congr fun j hj=>by simp [doneBatch,hj]

theorem batch_ok {σ s : State} {b p : Addr} {η off : Nat} (he : η=2∨η=4)
    (ho : off≤272) {L : Nat→List Zq} {X : Nat→List Byte}
    (hy : BatchLayout σ b p off X) (hs : BatchInv σ s b p L) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.batch true η off) s fun t=>
      BatchInv σ t b p (fun i=>rbFold η (L i) (X i)) := by
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.batch
  refine WP.seq (WP.mono (batchAt_init (η := η) (X := X) ho hs) fun e he0=>?_)
  refine WP.loop (M := isa) (fun m t=>∃ i,i<4 ∧ m=4-i ∧ BatchAt σ b p η off L X i t)
    (fun m t ⟨i,hi,hm,ht⟩=>?_) 4 e ⟨0,by decide,rfl,he0⟩
  subst hm
  refine WP.mono (batchAt_step he hi hy ht) fun t' ht'=>?_
  rw [batchAt_eval ht']
  by_cases hl : i+1=4
  · left
    rw [hl] at ht'
    exact ⟨by simp [hl],ht'.last⟩
  · right
    exact ⟨by simp; omega,4-(i+1),by omega,i+1,by omega,rfl,ht'⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
