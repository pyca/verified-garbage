module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitWord
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBody
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarPair
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
public import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMath
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `MlDsa.AArch64.Optimized.BoundedFourTraversal`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Sample

/-- Meaningful output after a prefix of a sampler stream. -/
def parsed (η : Nat) (L : List Zq) (X : List Byte) (done : Nat) : List Zq :=
 rbFold η L (X.take done)

theorem parsed_bound {η : Nat} {L : List Zq} {X : List Byte} (hL : L.length≤256) (done : Nat) :
    (parsed η L X done).length≤256 := rbFold_length_le hL _

theorem take_two {X : List Byte} {done : Nat} (h : done+2≤X.length) :
    X.take (done+2)=X.take done++[X[done]!,X[done+1]!] := by
  rw [show done+2=(done+1)+1 by omega_using [],List.take_succ_eq_append_getElem (by omega_using [h]),
    List.take_succ_eq_append_getElem (by omega_using [h]),List.append_assoc]
  simp only [getElem!_pos X done (by omega_using [h]),getElem!_pos X (done+1) (by omega_using [h])]
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

end

end

/-! ### `MlDsa.AArch64.Optimized.BoundedFourParseArgs`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Sample (movQ rbBound)

def scalarSetup (η : Nat) : List Instr :=
 [.movz .x .x6 256 0,.sub .x .x6 .x6 .x4,.lsl .x .x6 .x6 2,.add .x .x3 .x3 .x6,
 .movz .x .x5 272 0]++movQ .x9++
 [.movz .x .x10 (BitVec.ofNat 16 η) 0,.movz .x .x11 15 0,
  .movz .x .x15 (BitVec.ofNat 16 (rbBound η)) 0]

private theorem count_shift : ∀j≤256,
    ((256#64-BitVec.ofNat 64 (256-j))<<<2)=BitVec.ofNat 64 (4*j) := by
  intro j hj
  have hs:=BitVec.ofNat_sub_ofNat_of_le (w := 64) 256 (256-j) (by omega_using []) (by omega_using [])
  rw [hs,show 256-(256-j)=j by omega_using [hj],BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 j * BitVec.ofNat 64 4=BitVec.ofNat 64 (4*j)
  rw [←BitVec.ofNat_mul,Nat.mul_comm]

structure ScalarReady (η : Nat) (p : Addr) (j : Nat) (s : State) : Prop where
 output : s.gpr .x3=VG.Proof.MlDsa.Sample.coeffAddr p j
 bytes : s.gpr .x5=272
 q : s.gpr .x9=BitVec.ofNat 64 Spec.MlDsa.q
 eta : s.gpr .x10=BitVec.ofNat 64 η
 mask : s.gpr .x11=15
 bound : s.gpr .x15=BitVec.ofNat 64 (VG.Proof.MlDsa.Sample.rbB η)

theorem scalarSetup_ok {s : State} {η j : Nat} (he : η=2∨η=4) (hj : j≤256)
    {p : Addr} (h3 : s.gpr .x3=p) (h4 : s.gpr .x4=BitVec.ofNat 64 (256-j)) :
    WP isa (.block (scalarSetup η)) s fun t=>
      InitKeep [.x3,.x5,.x6,.x9,.x10,.x11,.x15] [] s t ∧ ScalarReady η p j t := by
  have hh : WP isa (.block (scalarSetup η)) s fun t=>
      (ScalarReady η p j t ∧ t.mem=s.mem) ∧ Keep [.x3,.x5,.x6,.x9,.x10,.x11,.x15] s t := by
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
    rcases he with rfl|rfl <;>
      unfold scalarSetup movQ <;>
      arun [h3,h4,count_shift j hj,VG.Proof.MlDsa.Sample.coeffAddr]
    all_goals constructor <;> simp [State.write,Size.bits,VG.Proof.MlDsa.Sample.coeffAddr,
      count_shift j hj,Spec.MlDsa.q,VG.Proof.MlDsa.Sample.rbB,rbBound]
  refine WP.mono (WP.keepV (by rfl) hh) fun t ⟨⟨⟨hc,hm⟩,hk⟩,hv⟩=>
    ⟨⟨hk,hm,fun _ _=>congrFun hv _⟩,hc⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

/-! ### `MlDsa.AArch64.Optimized.BoundedFourScalarLoop`, which the modules that import this one used -/

section

/-! ### `MlDsa.AArch64.Optimized.BoundedFourLoop`, which the modules that import this one used -/

section

/-! ## From `BoundedFourLoopState.lean` -/

@[expose] public section

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
    rw [List.mem_singleton.mp hr]; exact hY.streamApart) (by change X.length+2≤2^64; have:=hY.short; omega_using [this]) (by change i<X.length+2; omega_using [hi])]
  exact hY.stream i hi

theorem LoopInv.values {σ s : State} {η done : Nat} {table p q : Addr} {L : List Zq} {X : List Byte}
    (h : LoopInv σ η table p q L X done s) (hY : Layout σ table p q X) (hd : done+2≤X.length) :
    bodyValues η s=accepted η (nibbles X[done]! X[done+1]!) := by
  unfold bodyValues
  rw [h.input,h.stream hY (by omega_using [hd])]
  have ha : q+BitVec.ofNat 64 done+1=q+BitVec.ofNat 64 (done+1) := by
    rw [BitVec.add_assoc,BitVec.ofNat_add]; rfl
  rw [ha,h.stream hY (by omega_using [hd])]

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
    hL (by omega_using [hd]) h.stored h.output h.remaining h.bytes
    (by rw [h.keep.wr]; exact hY.write _ hL)) fun t ht=>?_
  have hl : parsed η L X (done+2)=parsed η L X done++bodyValues η s := by
    rw [parsed_two hη hd hL,h.values hY hd]
  have hbytes : X.length-(done+2)=(X.length-done)-2:=by omega_using []
  refine ⟨by omega_using [hd],by have:=h.even; omega_using [this],
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
  · rw [ite_eq_left hl,ne_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have:=hY.short; omega_using [this])]
    congr 1
    apply decide_eq_decide.mpr
    have:=h.bound
    omega_using [hl]
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
  have hd2 : d+2≤X.length:=by have:=hY.even; have:=hu.even; omega_arith
  refine WP.mono (vectorLoopStep_ok hη hY hu hd2 hl) fun v hv=>?_
  have he:=loopGuard_eval hY hv
  by_cases hc : d+2<X.length ∧ (parsed η L X (d+2)).length≤252
  · exact .inr ⟨by rw [he,decide_eq_true hc],X.length-(d+2),by omega_using [hd],
      d+2,rfl,hv,hc⟩
  · refine .inl ⟨by rw [he,decide_eq_false hc],d+2,hv,?_⟩
    omega_using [hd2, hc]

theorem loopGuard_zero {σ s : State} {η done : Nat} {table p q : Addr}
    {L : List Zq} {X : List Byte} (hY : Layout σ table p q X)
    (h : LoopInv σ η table p q L X done s) :
    isa.eval (.zero .x .x8) s=
      some (decide (done=X.length ∨ 252<(parsed η L X done).length)) := by
  rw [eval_zero,h.guard]
  by_cases hl : (parsed η L X done).length≤252
  · rw [ite_eq_left hl,eq_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have:=hY.short; omega_using [this])]
    congr 1
    apply decide_eq_decide.mpr
    have:=h.bound
    omega_using [hl, this]
  · rw [ite_eq_right hl]
    have hn : 252<(parsed η L X done).length:=by omega_using [hl]
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
      (fun _=>vectorLoop_ok hη hY h (by have:=h.bound; omega_using [he, this]) (by omega_using [he]))

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end

/-! ## From `BoundedFourScalarBody.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Sample (rbBody)

def scalarRegs : List Reg := [.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x12,.x13,.x14]

structure ScalarBodyPost (η : Nat) (s t : State) (p : Addr) (L : List Zq) : Prop where
 keep : Keep scalarRegs s t
 frame : Frame [polyR p] s.mem t.mem
 input : t.gpr .x2=s.gpr .x2+1
 bytes : t.gpr .x5=s.gpr .x5-1
 output : t.gpr .x3=coeffAddr p (rbStep η L (s.mem (s.gpr .x2))).length
 remaining : (t.gpr .x4).toNat=256-(rbStep η L (s.mem (s.gpr .x2))).length
 stored : Stored t.mem p (rbStep η L (s.mem (s.gpr .x2)))

theorem scalarBody_ok {η : Nat} (hη : η=2∨η=4) {s : State} {p : Addr} {L : List Zq}
    (hC : ScalarConsts η s) (hL : L.length≤256) (hS : Stored s.mem p L)
    (h3 : s.gpr .x3=coeffAddr p L.length) (h4 : (s.gpr .x4).toNat=256-L.length)
    (hR : InRegions (s.rd++s.wr) (s.gpr .x2) 1)
    (hW : ∀j<256,InRegions s.wr (coeffAddr p j) 4) :
    WP isa (rbBody η) s fun t=>ScalarBodyPost η s t p L := by
  change WP isa (.seq (.block VG.Impl.MlDsa.AArch64.Sample.rbLoad) (scalarPair η)) s _
  refine WP.seq (WP.mono (scalarLoad_ok hC.x11 hR) fun a ⟨hak,ha2,ha5,ha6,ha7⟩=>?_
    )
  refine WP.mono (scalarPair_ok hη (hC.keep hak.keep (by decide)) hL
    (by rw [hak.mem]; exact hS)
    (by rw [hak.get .x3]; exact h3) (by rw [hak.get .x4]; exact h4) ha6 ha7
    (fun j hj=>by rw [hak.wr]; exact hW j hj)) fun t ht=>?_
  refine ⟨(hak.keep.trans ht.keep).mono (by decide),?_,?_,?_,ht.output,ht.remaining,ht.stored⟩
  · rw [←hak.mem]; exact ht.frame
  · rw [ht.keep.gpr .x2 (by decide),ha2]
  · rw [ht.keep.gpr .x5 (by decide),ha5]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourScalarState.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

def parserRegs : List Reg := [.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17]
/-- What a batch's parse may write: the parser's registers and the loop's pointers. -/
abbrev batchRegs : List Reg := .x0::parserRegs++[.x24,.x25,.x26,.x27]

structure ScalarLayout (σ : State) (p q : Addr) (X : List Byte) : Prop where
 short : X.length≤272
 stream : ∀i<X.length,σ.mem (q+BitVec.ofNat 64 i)=X[i]!
 apart : (⟨q,X.length⟩ : Region).Disjoint (polyR p)
 read : ∀i<X.length,InRegions (σ.rd++σ.wr) (q+BitVec.ofNat 64 i) 1
 write : ∀j<256,InRegions σ.wr (coeffAddr p j) 4

structure ScalarInv (σ : State) (η : Nat) (p q : Addr) (L : List Zq) (X : List Byte)
    (done : Nat) (s : State) : Prop where
 bound : done≤X.length
 consts : ScalarConsts η s
 keep : Keep parserRegs σ s
 frame : Frame [polyR p] σ.mem s.mem
 stored : Stored s.mem p (parsed η L X done)
 input : s.gpr .x2=q+BitVec.ofNat 64 done
 output : s.gpr .x3=coeffAddr p (parsed η L X done).length
 remaining : (s.gpr .x4).toNat=256-(parsed η L X done).length
 bytes : s.gpr .x5=BitVec.ofNat 64 (X.length-done)
 guard : s.gpr .x8=BitVec.ofNat 64 ((256-(parsed η L X done).length)*(X.length-done))

theorem ScalarInv.stream {σ s : State} {η done : Nat} {p q : Addr} {L : List Zq} {X : List Byte}
    (h : ScalarInv σ η p q L X done s) (hy : ScalarLayout σ p q X) {i : Nat} (hi : i<X.length) :
    s.mem (q+BitVec.ofNat 64 i)=X[i]! := by
  rw [h.frame.bytes (R := ⟨q,X.length⟩) (fun r hr=>by
    rw [List.mem_singleton.mp hr]; exact hy.apart) (by change X.length≤2^64; have:=hy.short; omega_using [this]) hi]
  exact hy.stream i hi

theorem scalarGuard_ok {s : State} {r n : Nat}
    (h4 : (s.gpr .x4).toNat=r) (h5 : s.gpr .x5=BitVec.ofNat 64 n) :
    WP isa (.block [.mul .x .x8 .x4 .x5]) s fun t=>
      Only [.x8] s t ∧ t.gpr .x8=BitVec.ofNat 64 (r*n) := by
  have hh : s.gpr .x4=BitVec.ofNat 64 r := by rw [←h4]; simp
  refine wp_mul fun t ht he=>wp_nil ⟨ht,?_⟩
  rw [he,hh,h5,BitVec.ofNat_mul]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourScalarStep.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

theorem scalarStep_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {p q : Addr} {L : List Zq} {X : List Byte} (hl : L.length≤256)
    (hy : ScalarLayout σ p q X) (hi : ScalarInv σ η p q L X done s) (hd : done<X.length) :
    WP isa (.seq (VG.Impl.MlDsa.AArch64.Sample.rbBody η)
      (.block [.mul .x .x8 .x4 .x5])) s
      (ScalarInv σ η p q L X (done+1)) := by
  have hb := parsed_bound hl done (X := X) (η := η)
  have he : rbStep η (parsed η L X done) (s.mem (s.gpr .x2))=parsed η L X (done+1) := by
    rw [hi.input,hi.stream hy hd,parsed_one hd]
  refine WP.seq (WP.mono (scalarBody_ok hη hi.consts hb hi.stored hi.output hi.remaining
    (by rw [hi.input,hi.keep.rd,hi.keep.wr]; exact hy.read done hd)
    (fun j hj=>by rw [hi.keep.wr]; exact hy.write j hj)) fun t ht=>?_)
  rcases ht with ⟨htkeep,htframe,htinput,htbytes,htoutput,htremaining,htstored⟩
  rw [he] at htoutput htremaining htstored
  have ht5 : t.gpr .x5=BitVec.ofNat 64 (X.length-(done+1)) := by
    rw [htbytes,hi.bytes]
    have hh:=BitVec.ofNat_sub_ofNat_of_le (w := 64) (X.length-done) 1 (by decide) (by omega_using [hd])
    change BitVec.ofNat 64 (X.length-done)-1#64=_
    simpa only [show X.length-done-1=X.length-(done+1) by omega_using []] using hh
  refine WP.mono (scalarGuard_ok htremaining ht5) fun u ⟨hu,h8⟩=>?_
  have hk : Keep parserRegs σ u :=
    ((hi.keep.trans htkeep).trans hu.keep).mono (by decide)
  refine ⟨by omega_using [hd],(hi.consts.keep htkeep (by decide)).keep hu.keep (by decide),hk,?_,?_,?_,?_,?_,?_,h8⟩
  · rw [hu.mem]; exact hi.frame.trans htframe
  · rw [hu.mem]; exact htstored
  · rw [hu.get .x2,htinput,hi.input,BitVec.add_assoc,BitVec.ofNat_add]
    rfl
  · rw [hu.get .x3]; exact htoutput
  · rw [hu.get .x4]; exact htremaining
  · rw [hu.get .x5]; exact ht5

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourScalarLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

def ScalarDone (σ : State) (η : Nat) (p q : Addr) (L : List Zq) (X : List Byte)
    (s : State) : Prop := ∃done,ScalarInv σ η p q L X done s ∧
      (done=X.length ∨ (parsed η L X done).length=256)

def scalarLoopBody (η : Nat) : Prog isa :=
 .seq (VG.Impl.MlDsa.AArch64.Sample.rbBody η) (.block [.mul .x .x8 .x4 .x5])

theorem scalarGuard_nonzero {σ s : State} {η done : Nat} {p q : Addr}
    {L : List Zq} {X : List Byte} (hl : L.length≤256) (hy : ScalarLayout σ p q X)
    (hi : ScalarInv σ η p q L X done s) :
    isa.eval (.nonzero .x .x8) s=some (decide (done<X.length ∧ (parsed η L X done).length<256)) := by
  have hr : 256-(parsed η L X done).length≤256 := Nat.sub_le _ _
  have hn : X.length-done≤272 := by have:=hy.short; omega_using [this]
  have hp : (256-(parsed η L X done).length)*(X.length-done)<2^64 := by
    have:=Nat.mul_le_mul hr hn
    omega_using [this]
  rw [eval_nonzero,hi.guard,ne_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hp]
  congr 1
  apply decide_eq_decide.mpr
  rw [Nat.mul_ne_zero_iff]
  have:=hi.bound
  have:=parsed_bound (η := η) (X := X) hl done
  omega_using []

theorem scalarGuard_zero {σ s : State} {η done : Nat} {p q : Addr}
    {L : List Zq} {X : List Byte} (hl : L.length≤256) (hy : ScalarLayout σ p q X)
    (hi : ScalarInv σ η p q L X done s) :
    isa.eval (.zero .x .x8) s=some (decide (done=X.length ∨ (parsed η L X done).length=256)) := by
  have hn:=scalarGuard_nonzero hl hy hi
  rw [eval_nonzero] at hn
  rw [eval_zero]
  have h : (s.gpr .x8 != 0)=decide (done<X.length ∧ (parsed η L X done).length<256) := Option.some.inj hn
  have hb:=parsed_bound (η := η) (X := X) hl done
  have hd:=hi.bound
  by_cases he : done=X.length ∨ (parsed η L X done).length=256
  · have hn : ¬(done<X.length ∧ (parsed η L X done).length<256) := by omega_using [he]
    simp only [decide_eq_false hn] at h
    have hz : s.gpr .x8=0 := by simpa using h
    simp [hz,he]
  · have hn : done<X.length ∧ (parsed η L X done).length<256 := by omega_using [hb, hd, he]
    simp only [decide_eq_true hn] at h
    have hz : s.gpr .x8≠0 := by simpa using h
    simp only [decide_eq_false he,Option.some.injEq,beq_eq_false_iff_ne]
    exact hz

theorem scalarLoop_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {p q : Addr} {L : List Zq} {X : List Byte} (hl : L.length≤256)
    (hy : ScalarLayout σ p q X) (hi : ScalarInv σ η p q L X done s)
    (hd : done<X.length) (hn : (parsed η L X done).length<256) :
    WP isa (.loop (scalarLoopBody η) (.nonzero .x .x8)) s (ScalarDone σ η p q L X) := by
  refine WP.loop (M := isa)
    (fun rank s=>∃d,rank=X.length-d ∧ ScalarInv σ η p q L X d s ∧
      d<X.length ∧ (parsed η L X d).length<256) ?_ (X.length-done) s
    ⟨done,rfl,hi,hd,hn⟩
  rintro rank u ⟨d,rfl,hu,hd,hn⟩
  refine WP.mono (scalarStep_ok hη hl hy hu hd) fun v hv=>?_
  have he:=scalarGuard_nonzero hl hy hv
  by_cases hc : d+1<X.length ∧ (parsed η L X (d+1)).length<256
  · exact .inr ⟨by rw [he,decide_eq_true hc],X.length-(d+1),by omega_using [hd],d+1,rfl,hv,hc⟩
  · refine .inl ⟨by rw [he,decide_eq_false hc],d+1,hv,?_⟩
    have:=hv.bound
    have:=parsed_bound (η := η) (X := X) hl (d+1)
    omega_using [hd, hc, this]

theorem scalarPhase_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {p q : Addr} {L : List Zq} {X : List Byte} (hl : L.length≤256)
    (hy : ScalarLayout σ p q X) (hi : ScalarInv σ η p q L X done s) :
    WP isa (.ite (.zero .x .x8) (.block [])
      (.loop (scalarLoopBody η) (.nonzero .x .x8))) s (ScalarDone σ η p q L X) := by
  have he:=scalarGuard_zero hl hy hi
  by_cases hc : done=X.length ∨ (parsed η L X done).length=256
  · exact WP.ite true (by rw [he,decide_eq_true hc])
      (fun _=>WP.block_nil_iff.mpr ⟨done,hi,hc⟩) (fun h=>nomatch h)
  · exact WP.ite false (by rw [he,decide_eq_false hc]) (fun h=>nomatch h)
      (fun _=>scalarLoop_ok hη hl hy hi (by have:=hi.bound; omega_using [hc, this])
        (by have:=parsed_bound (η := η) (X := X) hl done; omega_using [hc, this]))

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end

/-! ## From `BoundedFourInitMiddle.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def middleSetup : List Instr :=
 [.vop (.dup .b16 .v23 .x11),.vop (.dup .s4 .v22 .x15),.vop (.dup .s4 .v21 .x9),
 .vop (.dup .s4 .v20 .x10),.vop (.add .s4 .v20 .v20 .v21),.movz .x .x6 13 0,
 .vop (.dup .s4 .v18 .x6),.movz .x .x6 5 0,.vop (.dup .s4 .v19 .x6)]

def initWord (x : BitVec 32) : BitVec 128 := ofVWords x x x x

structure MiddleConstants (η : Nat) (s : State) : Prop where
 nibble : s.v .v23=ofVBytes (fun _=>15)
 bound : s.v .v22=initWord (BitVec.ofNat 32 (VG.Proof.MlDsa.Sample.rbB η))
 q : s.v .v21=initWord 8380417
 etaQ : s.v .v20=initWord (BitVec.ofNat 32 (Spec.MlDsa.q+η))
 thirteen : s.v .v18=initWord 13
 five : s.v .v19=initWord 5

theorem middleSetup_ok {s : State} {η : Nat} (he : η=2∨η=4)
    (h9 : s.gpr .x9=BitVec.ofNat 64 Spec.MlDsa.q)
    (h10 : s.gpr .x10=BitVec.ofNat 64 η) (h11 : s.gpr .x11=15)
    (h15 : s.gpr .x15=BitVec.ofNat 64 (VG.Proof.MlDsa.Sample.rbB η)) :
    WP isa (.block middleSetup) s fun t=>
      InitKeep [.x6] [.v23,.v22,.v21,.v20,.v18,.v19] s t ∧ MiddleConstants η t := by
  unfold middleSetup
  refine wp_vop (d := .v23) rfl fun a ha=>wp_vop (d := .v22) rfl fun b hb=>
    wp_vop (d := .v21) rfl fun c hc=>wp_vop (d := .v20) rfl fun d hd=>
    wp_vop (d := .v20) rfl fun e he0=>?_
  refine wp_scalar (P := fun f=>Only [.x6] e f ∧ f.gpr .x6=13) (is := [.movz .x .x6 13 0]) rfl
    (wp_movz fun f hf h6=>wp_nil ⟨hf,h6⟩) fun f ⟨hf,h6⟩ hfv=>
    wp_vop (d := .v18) rfl fun g hg=>?_
  refine wp_scalar (P := fun h=>Only [.x6] g h ∧ h.gpr .x6=5) (is := [.movz .x .x6 5 0]) rfl
    (wp_movz fun h hh h5=>wp_nil ⟨hh,h5⟩) fun h ⟨hh,h5⟩ hhv=>
    wp_vop (d := .v19) rfl fun t ht=>wp_nil ?_
  have hk := ((((((((InitKeep.ofV ha (by decide)).trans (InitKeep.ofV hb (by decide))).trans
    (InitKeep.ofV hc (by decide))).trans (InitKeep.ofV hd (by decide))).trans
    (InitKeep.ofV he0 (by decide))).trans (InitKeep.ofOnly hf hfv)).trans
    (InitKeep.ofV hg (by decide))).trans (InitKeep.ofOnly hh hhv)).trans (InitKeep.ofV ht (by decide))
  refine ⟨hk.mono (by decide) (by decide),?_⟩
  constructor
  · rw [ht.other .v23 (by decide),hhv,hg.other .v23 (by decide),hfv,he0.other .v23 (by decide),hd.other .v23 (by decide),hc.other .v23 (by decide),hb.other .v23 (by decide),ha.v]
    rw [h11]
    rfl
  · rw [ht.other .v22 (by decide),hhv,hg.other .v22 (by decide),hfv,he0.other .v22 (by decide),hd.other .v22 (by decide),hc.other .v22 (by decide),hb.v]
    rw [ha.gpr,h15]
    rcases he with rfl|rfl <;> rfl
  · rw [ht.other .v21 (by decide),hhv,hg.other .v21 (by decide),hfv,he0.other .v21 (by decide),hd.other .v21 (by decide),hc.v]
    rw [hb.gpr,ha.gpr,h9]
    rfl
  · rw [ht.other .v20 (by decide),hhv,hg.other .v20 (by decide),hfv,he0.v]
    rw [hd.v,hd.other .v21 (by decide),hc.v,hc.gpr,hb.gpr,ha.gpr,h10,h9]
    rcases he with rfl|rfl <;> rfl
  · rw [ht.other .v18 (by decide),hhv,hg.v]
    rw [h6]
    rfl
  · rw [ht.v]
    rw [h5]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorSetup)

def setupFooter : List Instr :=
 [.movz .x .x0 0 0,.movz .x .x16 4 0,.addImm .x .x12 .x19 3000,.addImm .x .x12 .x12 3000]

theorem setupFooter_ok (s : State) :
    WP isa (.block setupFooter) s fun t=>InitKeep [.x0,.x16,.x12] [] s t ∧
      t.gpr .x0=0 ∧ t.gpr .x16=4 ∧ t.gpr .x12=s.gpr .x19+6000 := by
  let P : State→Prop := fun t=>Only [.x0,.x16,.x12] s t ∧
    t.gpr .x0=0 ∧ t.gpr .x16=4 ∧ t.gpr .x12=s.gpr .x19+6000
  apply WP.mono (WP.keepV (is := setupFooter) (Q := P) (by decide) ?_)
  · intro t ⟨⟨ho,h0,h16,h12⟩,hv⟩
    exact ⟨InitKeep.ofOnly ho hv,h0,h16,h12⟩
  change WP isa (.block setupFooter) s P
  dsimp only [P]
  unfold setupFooter
  refine wp_movz fun a ha h0=>wp_movz fun b hb h16=>
    wp_addImm (by decide) fun c hc h12=>wp_addImm (by decide) fun t ht h12'=>wp_nil ?_
  refine ⟨(((ha.trans hb).trans hc).trans ht).mono (by decide),?_,?_,?_⟩
  · rw [ht.get .x0,hc.get .x0,hb.get .x0,h0]; rfl
  · rw [ht.get .x16,hc.get .x16,h16]; rfl
  · rw [h12',h12,hb.get .x19,ha.get .x19,BitVec.add_assoc]; rfl

theorem vectorSetup_eq (η : Nat) : vectorSetup η=
    pairSetup .v25 0xffffff01ffffff00 0xffffff03ffffff02 ++ middleSetup ++
      pairSetup .v24 0x0000000200000001 0x0000000800000004 ++ setupFooter := rfl

theorem initWord_lane (x : BitVec 32) {e : Nat} (he : e<4) : vword (initWord x) e=x := by
  unfold initWord
  rw [VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
  rcases (show e=0∨e=1∨e=2∨e=3 by omega_using [he]) with rfl|rfl|rfl|rfl <;> rfl

private theorem weights_lane : ∀e<4,
    vword (ofVDwords 0x0000000200000001 0x0000000800000004) e=BitVec.ofNat 32 (2^e) := by decide

theorem vectorSetup_ok {s : State} {η : Nat} (he : η=2∨η=4)
    (h9 : s.gpr .x9=BitVec.ofNat 64 Spec.MlDsa.q)
    (h10 : s.gpr .x10=BitVec.ofNat 64 η) (h11 : s.gpr .x11=15)
    (h15 : s.gpr .x15=BitVec.ofNat 64 (VG.Proof.MlDsa.Sample.rbB η)) :
    WP isa (.block (vectorSetup η)) s fun t=>
      InitKeep [.x0,.x6,.x7,.x12,.x16] constantVecs s t ∧ Consts η (s.gpr .x19+6000) t := by
  rw [vectorSetup_eq,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (pairSetup_ok s .v25 _ _ (by decide)) fun a ⟨ha,h25⟩=>?_
  rw [WP.block_append_iff]
  refine WP.mono (middleSetup_ok he (by rw [ha.keep.gpr .x9 (by decide)]; exact h9)
    (by rw [ha.keep.gpr .x10 (by decide)]; exact h10)
    (by rw [ha.keep.gpr .x11 (by decide)]; exact h11)
    (by rw [ha.keep.gpr .x15 (by decide)]; exact h15)) fun b ⟨hb,hbC⟩=>?_
  rw [WP.block_append_iff]
  refine WP.mono (pairSetup_ok b .v24 _ _ (by decide)) fun c ⟨hc,h24⟩=>?_
  refine WP.mono (setupFooter_ok c) fun t ⟨ht,h0,h16,h12⟩=>?_
  have hk := ((ha.trans hb).trans hc).trans ht
  have hc19 : c.gpr .x19=s.gpr .x19 := ((ha.trans hb).trans hc).keep.gpr _ (by decide)
  refine ⟨hk.mono (by decide) (by decide),?_⟩
  constructor
  · exact h0
  · rw [hk.keep.gpr .x11 (by decide)]; exact h11
  · rw [h12,hc19]
  · exact h16
  · intro e he
    rw [ht.vec .v18 (by decide),hc.vec .v18 (by decide),hbC.thirteen,initWord_lane _ he]
    rfl
  · intro e he
    rw [ht.vec .v19 (by decide),hc.vec .v19 (by decide),hbC.five,initWord_lane _ he]
    rfl
  · intro e he
    rw [ht.vec .v20 (by decide),hc.vec .v20 (by decide),hbC.etaQ,initWord_lane _ he]
  · intro e he
    rw [ht.vec .v21 (by decide),hc.vec .v21 (by decide),hbC.q,initWord_lane _ he]
    rfl
  · intro e he
    rw [ht.vec .v22 (by decide),hc.vec .v22 (by decide),hbC.bound,initWord_lane _ he]
  · rw [ht.vec .v23 (by decide),hc.vec .v23 (by decide),hbC.nibble]
  · intro e he
    rw [ht.vec .v24 (by decide),h24]
    exact weights_lane e he
  · rw [ht.vec .v25 (by decide),hc.vec .v25 (by decide),hb.vec .v25 (by decide),h25]
    rfl
  · rw [hk.keep.gpr .x9 (by decide)]; exact h9
  · rw [hk.keep.gpr .x10 (by decide)]; exact h10
  · rw [hk.keep.gpr .x15 (by decide)]; exact h15

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
