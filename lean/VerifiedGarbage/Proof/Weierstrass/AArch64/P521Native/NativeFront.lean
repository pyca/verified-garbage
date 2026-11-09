module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildInitial
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildLoopTransfer
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.CountedLoop
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizePrefixInv
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.Normalize
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowData
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeFrontPreserve
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.Prepare
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareStack
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareSelected

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- The selected measured loop has exactly the existing verified bit-extraction body. -/
theorem recode_body_source : VG.Impl.Weierstrass.AArch64.P521Native.outerBlock006=bitsBody 3944 3304 := by lit_decide

theorem recode_loop_ok {s : State} {base : Addr} (hs : Scr s base 8192)
    (counter : s.gpr .x19=BitVec.ofNat 64 80) (one : s.gpr .x5=1) :
    WP isa VG.Impl.Weierstrass.AArch64.P521Native.loop21 s fun t =>
      (∀j<640,t.mem (off base (3304+j))=if (wordsVal s.mem base 3944 10).testBit j then 1 else 0) ∧
      KeepRegs [.x1,.x2,.x5,.x16,.x17,.x19] s t ∧ Outside base 3304 640 s.mem t.mem ∧ t.gpr .x19=0 := by
  have initial : BInv base 8192 3944 3304 10 s s 80 :=
    ⟨hs,one,counter,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _,by intro j hj hj'; omega_arith⟩
  rw [VG.Impl.Weierstrass.AArch64.P521Native.loop21]
  refine countLoop_ok (Inv:=fun i t => BInv base 8192 3944 3304 10 s t i) (n:=80) (by decide)
    (fun j u h1 h2 inv => ?_) (fun t inv => ?_) (by decide) initial
  · obtain ⟨i,rfl⟩ : ∃i,j=i+1 := ⟨j-1,by omega_arith⟩
    have body := bitsBody_ok inv.scr inv.x19 (by omega_arith) inv.x5 (by omega_arith)
      (by decide : 3944<4096) (by omega_arith) (by decide : 3304+8≤4096)
    rw [VG.Impl.Weierstrass.AArch64.P521Native.sequence,List.foldr_cons,List.foldr_nil,recode_body_source]
    refine WP.seq (WP.mono body fun v ⟨count,k,done,outside⟩ => ?_)
    have hbyte : u.mem (off base (3944+i))=s.mem (off base (3944+i)) :=
      inv.mem _ (by rw [ofs_off0 base (d:=3944+i) (by omega_arith)]; omega_arith)
    have next : BInv base 8192 3944 3304 10 s v i := by
      refine ⟨inv.scr.of_keepRegs k (by decide),(k.gpr _ (by decide)).trans inv.x5,count,
        inv.keep.trans (k.mono (by simp)),inv.mem.trans (outside.mono (by omega_arith) (by omega_arith)),?_⟩
      intro bit hb hb'
      rcases Nat.lt_or_ge bit (8*(i+1)) with hlo|hhi
      · have e := done (bit-8*i) (by omega_arith)
        rw [show 8*i+(bit-8*i)=bit by omega_arith,hbyte] at e
        rw [e,show bit/8=i by omega_arith,show bit%8=bit-8*i by omega_arith]
      · rw [outside _ (by rw [ofs_off0 base (d:=3304+bit) (by omega_arith)]; omega_arith),inv.bits bit hhi hb']
    exact WP.block_nil ⟨by simpa only [Nat.add_sub_cancel] using next,by simpa only [Nat.add_sub_cancel] using count⟩
  · refine ⟨?_,inv.keep,inv.mem,inv.x19⟩
    intro bit hb
    rw [inv.bits bit (by omega_arith) hb,
      show bit=8*(bit/8)+bit%8 from (Nat.div_add_mod bit 8).symm,
      testBit_byte s.mem base (a:=3944) (n:=10) (by omega_arith) (Nat.mod_lt _ (by decide))]
    simp only [show (8*(bit/8)+bit%8)/8=bit/8 by omega_arith,
      show (8*(bit/8)+bit%8)%8=bit%8 by omega_arith]

theorem recode_scalar_ok {s : State} {base : Addr} (hs : Scr s base 8192)
    (counter : s.gpr .x19=BitVec.ofNat 64 80) (one : s.gpr .x5=1) :
    WP isa VG.Impl.Weierstrass.AArch64.P521Native.recodeScalar s fun t =>
      (∀j<640,t.mem (off base (3304+j))=if (wordsVal s.mem base 3944 10).testBit j then 1 else 0) ∧
      KeepRegs [.x1,.x2,.x5,.x16,.x17,.x19] s t ∧ Outside base 3304 640 s.mem t.mem ∧ t.gpr .x19=0 := by
  rw [VG.Impl.Weierstrass.AArch64.P521Native.recodeScalar,VG.Impl.Weierstrass.AArch64.P521Native.sequence,List.foldr_cons,List.foldr_nil]
  exact WP.seq (WP.mono (recode_loop_ok hs counter one) fun _ h => WP.block_nil h)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

theorem build_initial_loop_wp {s : State} {Q : State → Prop} :
    WP isa buildTable s Q ↔ WP isa (.seq buildInitial loop22) s Q := by
  rw [build_table_phases_wp]
  simp only [sequence,List.foldr_cons,List.foldr_nil,buildInitial,buildSeed,buildSeedTail,buildAdvance]
  rw [build_seed_source,build_seed_tail_source]
  simp only [WP.seq_iff (M:=isa),WP.block_append_iff (M:=isa),WP.block_nil_iff (M:=isa)]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

theorem normalize_phases_machine_wp {s : State} {Q : State → Prop} :
    WP isa normalizeAndInit s Q ↔ WP isa normalizePhases s Q := by
  have p : normalizeCodePrefix=normalizePrefixMachine := rfl
  have i : normalizeCodeInverse=normalizeInverseMachine := rfl
  have b0 : normalizeCodeBack0=normalizeBackChunk0 := rfl
  have b1 : normalizeCodeBack1=normalizeBackChunk1 := rfl
  have b2 : normalizeCodeBack2=normalizeBackChunk2 := rfl
  rw [normalizeAndInit,normalizePhases,normalizeBackMachine,p,i,b0,b1,b2]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass Spec.Weierstrass

theorem build_loop_inv_update {C : Curve} {base table : Addr} {P : Point C} {m : Nat} {s t : State}
    (layout : NormalizeLayout base table 8192) (inv : BuildLoopInv C base table P m s)
    (lo : 2≤m) (hi : m<16) (ctx : NormalizeContext base table 8192 t)
    (ptr : t.gpr .x20=off table (216*(m+1))) (count : t.gpr .x19=BitVec.ofNat 64 (16-(m+1)))
    (currentBounds : canonicalPoint t.mem base 1504)
    (currentValue : InvJ C (pointAt C t.mem base 1504).1 (pointAt C t.mem base 1504).2.1
      (pointAt C t.mem base 1504).2.2 (mul (m+1) P))
    (rowBounds : ∀c,c<3 → wordsVal t.mem table (216*m+72*c) 9<fieldPrime)
    (rowValue : InvJ C (pointAt C t.mem table (216*m)).1 (pointAt C t.mem table (216*m)).2.1
      (pointAt C t.mem table (216*m)).2.2 (mul (m+1) P))
    (frame : BuildLoopFrame base table m 216 s.mem t.mem) : BuildLoopInv C base table P (m+1) t := by
  have same (d : Nat) (hd : d+72≤8192) (hw : d+72≤1288 ∨ 2152≤d) (hs : d+72≤3952 ∨ 4024≤d) :
      wordsVal t.mem base d 9=wordsVal s.mem base d 9 :=
    frame.workspace_words layout.tableApart (by decide) (by omega_arith) 9 d hd hw hs
  have sameX:=same 2800 (by decide) (Or.inr (by decide)) (Or.inl (by decide))
  have sameY:=same 3160 (by decide) (Or.inr (by decide)) (Or.inl (by decide))
  have tableSame (i c : Nat) (ih : i<m) (ch : c<3) :
      wordsVal t.mem table (216*i+72*c) 9=wordsVal s.mem table (216*i+72*c) 9 :=
    frame.table_words layout.tableApart (by decide) 9 _ (by omega_arith) (Or.inl (by omega_arith))
  refine ⟨ctx,ptr,count,by rw [sameX]; exact inv.peerX,by rw [sameY]; exact inv.peerY,
    ?_,currentBounds,currentValue,?_,?_,?_,?_⟩
  · simpa only [peerPoint,sameX,sameY] using inv.peerValue
  · intro i ih c ch
    by_cases he : i=m
    · subst i; exact rowBounds c ch
    · rw [tableSame i c (by omega_arith) ch]
      exact inv.tableBounds i (by omega_arith) c ch
  · intro i ih
    by_cases he : i=m
    · subst i; exact rowValue
    · have hp : pointAt C t.mem table (216*i)=pointAt C s.mem table (216*i) :=
        pointAt_copy (fun c ch => tableSame i c (by omega_arith) ch)
      rw [hp]
      exact inv.tableValue i (by omega_arith)
  · have hz:=tableSame 0 2 (by omega_arith) (by decide)
    simpa only [Nat.mul_zero,Nat.zero_add,Nat.reduceMul,hz] using inv.tableFirstZ
  · rw [same 424 (by decide) (Or.inl (by decide)) (Or.inl (by decide))]
    exact inv.oneField

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass Spec.Weierstrass

private theorem context_keep {base table : Addr} {s t : State} {rs : List Reg}
    (ctx : NormalizeContext base table 8192 s) (k : KeepRegs rs s t)
    (h0 : Reg.x0∉rs) (h26 : Reg.x26∉rs) : NormalizeContext base table 8192 t :=
  ⟨ctx.workspace.of_keepRegs k h0,ctx.readTable.of_keepRegs k h26,ctx.tableW.of_keepRegs k h26⟩

private theorem advance_v31 {s : State} {Q : State → Prop} (h : WP isa buildAdvance s Q) :
    WP isa buildAdvance s fun t => Q t ∧ t.v .v31=s.v .v31 := by
  obtain ⟨trace,t,exec,q⟩:=h
  exact ⟨trace,t,exec,q,Exec.vec (c:=buildAdvance) (r:=.v31) (by decide) exec⟩

theorem build_loop_step_ok {C : Curve} (hp : C.p=fieldPrime) (law : Law C) (ha : AM3 C)
    (order : PrimeOrder C) {P : Point C} (oncurve : onCurve C P=true) (pne : P≠.infinity)
    (orderBound : 17≤C.n) {base table : Addr} {m : Nat} {s : State}
    (layout : NormalizeLayout base table 8192) (inv : BuildLoopInv C base table P m s)
    (lo : 2≤m) (hi : m<16) :
    WP isa buildLoopStep s fun t =>
      BuildLoopInv C base table P (m+1) t ∧ BuildLoopFrame base table m 216 s.mem t.mem ∧
      t.sp=s.sp ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.v .v31=s.v .v31 ∧
      (∀r∈[Reg.x26,Reg.x27,Reg.x28,Reg.x30],t.gpr r=s.gpr r) := by
  rw [buildLoopStep,WP.seq_iff]
  have peerCurve : onCurve C (peerPoint C s.mem base)=true := by rw [inv.peerValue]; exact oncurve
  have separate : mul m P≠peerPoint C s.mem base := by
    rw [inv.peerValue]
    exact (Window5.tbl_noexc law order oncurve pne orderBound lo (by omega_arith)).1
  refine WP.mono (build_mixed_group hp law ha inv.context.workspace (by decide) (by decide)
    inv.peerX inv.peerY inv.currentBounds.1 inv.currentBounds.2.1 inv.currentBounds.2.2
    (law.onCurve_mul oncurve m) peerCurve inv.currentValue
    (Window5.mul_ne_infinity order oncurve pne (by omega_arith) (by omega_arith)) separate)
    fun a ⟨bound,point,hsA,publicA,frameA⟩ => ?_
  have ctxA:=inv.context.of_public hsA publicA
  have invPtr : a.gpr .x20=off table (216*m) := (publicA.gpr .x20 (by decide)).trans inv.writePointer
  have ptrA : PtrW a .x20 (off table (216*m)) 216 :=
    ⟨invPtr,by intro d hd; rw [publicA.wr]; exact (inv.write_row hi).st d hd,
      (inv.write_row hi).enc,(inv.write_row hi).nowrap⟩
  rw [WP.seq_iff]
  refine WP.mono (advance_v31 (build_advance_ok hsA ptrA (inv.row_apart layout hi)))
    fun b ⟨⟨tb,eb,kb,crossB,frameB⟩,v31B⟩ => ?_
  refine WP.mono (build_counter_ok b) fun t ⟨gp20,gp19,kt,vt⟩ => ?_
  have regsT : KeepRegs [.x20,.x19] b t := Keeps.regs kt
  have ctxB:=context_keep ctxA kb (by decide) (by decide)
  have ctxT:=context_keep ctxB regsT (by decide) (by decide)
  have output (c : Nat) (hc : c<3) : wordsVal a.mem base (1288+72*c) 9<fieldPrime := by
    have cases : c=0 ∨ c=1 ∨ c=2 := by omega_arith
    rcases cases with rfl|rfl|rfl
    · simpa only [Nat.mul_zero,Nat.add_zero] using bound.1
    · simpa only [Nat.mul_one,Nat.reduceAdd] using bound.2.1
    · simpa only [Nat.reduceMul,Nat.reduceAdd] using bound.2.2
  have rowCopy (c : Nat) (hc : c<3) : wordsVal t.mem table (216*m+72*c) 9=wordsVal a.mem base (1288+72*c) 9 := by
    rw [kt.mem,←VG.Proof.Weierstrass.AArch64.Mont.wordsVal_off b.mem table (216*m) (72*c) 9]
    exact tb c hc
  have currentCopy (c : Nat) (hc : c<3) : wordsVal t.mem base (1504+72*c) 9=wordsVal a.mem base (1288+72*c) 9 := by
    rw [kt.mem]; exact eb c hc
  have currentEqual:=pointAt_copy currentCopy (C:=C)
  have rowEqual:=pointAt_copy rowCopy (C:=C)
  have sum : Spec.Weierstrass.add (mul m P) (peerPoint C s.mem base)=mul (m+1) P := by
    rw [inv.peerValue]
    exact (congrArg (Spec.Weierstrass.add (mul m P)) (mul_one_pt P).symm).trans (law.add_mul_mul oncurve m 1)
  rw [sum] at point
  have currentPoint : InvJ C (pointAt C t.mem base 1504).1 (pointAt C t.mem base 1504).2.1
      (pointAt C t.mem base 1504).2.2 (mul (m+1) P) := by rw [currentEqual]; exact point
  have rowPoint : InvJ C (pointAt C t.mem table (216*m)).1 (pointAt C t.mem table (216*m)).2.1
      (pointAt C t.mem table (216*m)).2.2 (mul (m+1) P) := by rw [rowEqual]; exact point
  have currentBound : canonicalPoint t.mem base 1504 := by
    have bx:=output 0 (by decide); have byY:=output 1 (by decide); have bz:=output 2 (by decide)
    rw [←currentCopy 0 (by decide)] at bx
    rw [←currentCopy 1 (by decide)] at byY
    rw [←currentCopy 2 (by decide)] at bz
    exact ⟨bx,byY,bz⟩
  have frameAB : BuildLoopFrame base table m 216 s.mem b.mem :=
    (BuildLoopFrame.of_mixed frameA |>.mono (by decide)).trans (.of_advance hi crossB frameB)
  have frame : BuildLoopFrame base table m 216 s.mem t.mem := by rw [kt.mem]; exact frameAB
  have pointer : t.gpr .x20=off table (216*(m+1)) := by
    rw [gp20,kb.gpr .x20 (by decide),invPtr]
    exact build_counter_pointer
  have count : t.gpr .x19=BitVec.ofNat 64 (16-(m+1)) := by
    rw [gp19,kb.gpr .x19 (by decide),publicA.gpr .x19 (by decide),inv.counter]
    exact build_counter_count m hi
  refine ⟨build_loop_inv_update layout inv lo hi ctxT pointer count currentBound currentPoint
    (fun c hc => by rw [rowCopy c hc]; exact output c hc) rowPoint frame,frame,
    kt.sp.trans (kb.sp.trans publicA.sp),kt.rd.trans (kb.rd.trans publicA.rd),kt.wr.trans (kb.wr.trans publicA.wr),
    (congrFun vt .v31).trans (v31B.trans publicA.v31),?_⟩
  intro r hr
  have choices : r=Reg.x26 ∨ r=Reg.x27 ∨ r=Reg.x28 ∨ r=Reg.x30 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hr
  rcases choices with rfl|rfl|rfl|rfl
  all_goals exact (kt.gpr _ (by decide)).trans ((kb.gpr _ (by decide)).trans (publicA.gpr _ (by decide)))

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass Spec.Weierstrass
open VG.Impl.Weierstrass.AArch64.P521Native (loop22)

theorem BuildLoopFrame.whole {base table : Addr} {row : Nat} {m m' : Mem}
    (frame : BuildLoopFrame base table row 216 m m') (hi : row<16) :
    BuildLoopFrame base table 0 3456 m m' := by
  intro x hw hs ht
  apply frame x hw hs
  omega_arith

theorem build_loop_ok {C : Curve} (hp : C.p=fieldPrime) (law : Law C) (ha : AM3 C)
    (order : PrimeOrder C) {P : Point C} (oncurve : onCurve C P=true) (pne : P≠.infinity)
    (orderBound : 17≤C.n) {base table : Addr} {s : State}
    (layout : NormalizeLayout base table 8192) (inv : BuildLoopInv C base table P 2 s) :
    WP isa loop22 s fun t => BuildLoopInv C base table P 16 t ∧
      BuildLoopFrame base table 0 3456 s.mem t.mem ∧ t.sp=s.sp ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      t.v .v31=s.v .v31 ∧ (∀r∈[Reg.x26,Reg.x27,Reg.x28,Reg.x30],t.gpr r=s.gpr r) := by
  let I : Nat → State → Prop := fun m t => 2≤m ∧ BuildLoopInv C base table P m t ∧
    BuildLoopFrame base table 0 3456 s.mem t.mem ∧ t.sp=s.sp ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
    t.v .v31=s.v .v31 ∧ (∀r∈[Reg.x26,Reg.x27,Reg.x28,Reg.x30],t.gpr r=s.gpr r)
  have start : I 2 s := ⟨by decide,inv,.refl base table 0 3456 s.mem,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
  unfold loop22
  refine WP.mono (WP.chunk_loop (I:=I) (n:=16) (k:=2) (N:=1) (by decide) (by decide) start ?_ ?_)
    fun t out => ?_
  · intro m t hm ht
    rcases ht with ⟨lo,it,ft,st,rt,wt,vt,gt⟩
    apply build_loop_step_wp.mpr
    refine WP.mono (build_loop_step_ok hp law ha order oncurve pne orderBound layout it lo (by omega_arith))
      fun u ⟨iu,fu,su,ru,wu,vu,gu⟩ => ?_
    exact ⟨by omega_arith,iu,ft.trans (fu.whole (by omega_arith)),su.trans st,ru.trans rt,wu.trans wt,vu.trans vt,
      fun r hr => (gu r hr).trans (gt r hr)⟩
  · intro m t hm ht
    rcases ht with ⟨_,it,_,_,_,_,_,_⟩
    constructor
    · intro close
      have eq : m=16 := by omega_arith
      change some (t.read .x .x19 != 0)=some false
      change some (t.gpr .x19 != 0)=some false
      rw [it.counter,eq]
      rfl
    · intro more
      have bound : 16-m<2^64 := by omega_arith
      have ne : BitVec.ofNat 64 (16-m)≠0 := by
        intro eq
        have same:=congrArg BitVec.toNat eq
        change (16-m)%2^64=0 at same
        rw [Nat.mod_eq_of_lt bound] at same
        omega_arith
      change some (t.read .x .x19 != 0)=some true
      change some (t.gpr .x19 != 0)=some true
      rw [it.counter]
      simp only [bne_eq,beq_eq_false_iff_ne.mpr ne,Bool.not_false]
  · rcases out with ⟨j,hj,close,it⟩
    rcases it with ⟨_,ij,fj,sj,rj,wj,vj,gj⟩
    have eq : j=16 := by omega_arith
    subst j
    exact ⟨ij,fj,sj,rj,wj,vj,gj⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass Spec.Weierstrass

def buildTableField (m : Mem) (table : Addr) (c i : Nat) : Fin fieldPrime :=
  Fin.ofNat fieldPrime (wordsVal m table (216*i+72*c) 9)

theorem BuildLoopInv.normalize_start {C : Curve} {base table : Addr} {P : Point C} {s : State}
    (inv : BuildLoopInv C base table P 16 s) :
    NormalizePrefixInv base table 8192 1 s (buildTableField s.mem table 0)
      (buildTableField s.mem table 1) (buildTableField s.mem table 2) := by
  have nz := inv.tableBounds 0 (by decide) 2 (by decide)
  simp only [Nat.mul_zero,Nat.zero_add,Nat.reduceMul] at nz
  apply normalize_prefix_start inv.context
  · refine ⟨?_,?_,?_,?_⟩
    · intro i hi c hc
      exact inv.tableBounds i hi c hc
    · intro i hi; rfl
    · intro i hi; rfl
    · intro i hi; rfl
  · rw [inv.oneField,←inv.tableFirstZ]
    exact nz
  · simp only [buildTableField,Nat.mul_zero,Nat.zero_add,Nat.reduceMul]
    rw [inv.oneField,inv.tableFirstZ]

theorem BuildLoopInv.workspace_readonly {base table : Addr} {s t : State}
    (layout : NormalizeLayout base table 8192)
    (frame : BuildLoopFrame base table 0 3456 s.mem t.mem) {d : Nat} (hd : d<8192)
    (outside : d<1288 ∨ 2152≤d) (scratch : d<3952 ∨ 4024≤d) :
    t.mem (off base d)=s.mem (off base d) :=
  frame.workspace_byte layout.tableApart (by decide) (by decide) hd outside scratch

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass Spec.Weierstrass

theorem native_affine_coordinate_transfer {C : Curve} {p : Nat} [NeZero p] (hp : C.p=p) (law : Law C)
    (order : PrimeOrder C) {P : Point C} (oncurve : onCurve C P=true) (pne : P≠.infinity)
    (orderBound : 17≤C.n) (X Y Z OX OY : Nat → Nat)
    (original : ∀i,i<16 → InvJ C (Fin.ofNat C.p (X i)) (Fin.ofNat C.p (Y i)) (Fin.ofNat C.p (Z i)) (mul (i+1) P))
    (first : Z 0=1)
    (xvalue : ∀i,i<16 → Fin.ofNat p (OX i)=
      (normalizeBackResult (fun i => Fin.ofNat p (Z i)) (normalizeProduct (fun i => Fin.ofNat p (Z i))) 15
        (fun i => Fin.ofNat p (X i)) (fun i => Fin.ofNat p (Y i))
        (normalizeProduct (fun i => Fin.ofNat p (Z i)) 16^(p-2))).1 i)
    (yvalue : ∀i,i<16 → Fin.ofNat p (OY i)=
      (normalizeBackResult (fun i => Fin.ofNat p (Z i)) (normalizeProduct (fun i => Fin.ofNat p (Z i))) 15
        (fun i => Fin.ofNat p (X i)) (fun i => Fin.ofNat p (Y i))
        (normalizeProduct (fun i => Fin.ofNat p (Z i)) 16^(p-2))).2.1 i) :
    ∀i,i<16 → RepA C (Fin.ofNat C.p (OX i)) (Fin.ofNat C.p (OY i)) 1 (mul (i+1) P) := by
  rcases C with ⟨q,a,b,gx,gy,n,len,qnz,nnz⟩
  dsimp only at hp
  subst q
  have nonzero (i : Nat) (hi : i<16) : (Fin.ofNat p (Z i) : Fin p)≠0 := by
    intro eq
    have zeroPoint := ((original i hi).z_zero_iff law).mp eq
    exact Window5.mul_ne_infinity order oncurve pne (by omega_arith) (by omega_arith) zeroPoint
  have one : (Fin.ofNat p (Z 0) : Fin p)=1 := by rw [first]; rfl
  have affine:=normalize_back_affine_rows law (fun i => Fin.ofNat p (X i)) (fun i => Fin.ofNat p (Y i))
    (fun i => Fin.ofNat p (Z i)) (fun i => mul (i+1) P) original nonzero one
  intro i hi
  rw [xvalue i hi,yvalue i hi]
  exact affine i hi

theorem native_front_table_affine {C : Curve} (hp : C.p=fieldPrime) (law : Law C)
    (order : PrimeOrder C) {P : Point C} (oncurve : onCurve C P=true) (pne : P≠.infinity)
    (orderBound : 17≤C.n) {base table : Addr} {s t : State}
    (build : BuildLoopInv C base table P 16 s)
    (normal : NormalizePost base table s t (buildTableField s.mem table 0)
      (buildTableField s.mem table 1) (buildTableField s.mem table 2)) :
    ∀i,i<16 → RepA C (Fin.ofNat C.p (wordsVal t.mem table (216*i) 9))
      (Fin.ofNat C.p (wordsVal t.mem table (216*i+72) 9)) 1 (mul (i+1) P) := by
  apply native_affine_coordinate_transfer hp law order oncurve pne orderBound
    (fun i => wordsVal s.mem table (normalizeEntrySlot i 0) 9) (fun i => wordsVal s.mem table (normalizeEntrySlot i 1) 9)
    (fun i => wordsVal s.mem table (normalizeEntrySlot i 2) 9)
    (fun i => wordsVal t.mem table (normalizeEntrySlot i 0) 9) (fun i => wordsVal t.mem table (normalizeEntrySlot i 1) 9)
  · intro i hi
    exact build.tableValue i hi
  · simpa only [normalizeEntrySlot,Nat.mul_zero,Nat.zero_add,Nat.reduceMul] using build.tableFirstZ
  · intro i hi
    exact normal.tableValues.xValue i hi
  · intro i hi
    exact normal.tableValues.yValue i hi

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass

def buildInitialWrites : List (Nat × Nat) := [(1288,864),(3944,80),(8192,2^64)]
def buildLoopWrites : List (Nat × Nat) := [(1288,864),(3952,72),(8192,2^64)]

theorem BuildInitialFrame.workspace_unch {base table : Addr} {m m' : Mem}
    (frame : BuildInitialFrame base table m m') (layout : NormalizeLayout base table 8192) :
    Unch base buildInitialWrites m m' := by
  intro x hx
  have h1:=hx (1288,864) (by simp [buildInitialWrites])
  have h2:=hx (3944,80) (by simp [buildInitialWrites])
  have h3:=hx (8192,2^64) (by simp [buildInitialWrites])
  have inWorkspace : (⟨base,8192⟩ : Region).Contains x 1 := by
    change ofs base x+1≤8192
    have addrBound : ofs base x<2^64 := BitVec.isLt _
    simp only at h3
    omega_arith
  have outTable := layout.tableApart.disjoint x inWorkspace
  have tableFar : 3456≤ofs table x := by
    change ¬ofs table x+1≤3456 at outTable
    omega_arith
  apply frame x (by simpa only using h1) (by simpa only using h2) (Or.inr (by omega_arith))

theorem BuildLoopFrame.workspace_unch {base table : Addr} {m m' : Mem}
    (frame : BuildLoopFrame base table 0 3456 m m') (layout : NormalizeLayout base table 8192) :
    Unch base buildLoopWrites m m' := by
  intro x hx
  have h1:=hx (1288,864) (by simp [buildLoopWrites])
  have h2:=hx (3952,72) (by simp [buildLoopWrites])
  have h3:=hx (8192,2^64) (by simp [buildLoopWrites])
  have inWorkspace : (⟨base,8192⟩ : Region).Contains x 1 := by
    change ofs base x+1≤8192
    have addrBound : ofs base x<2^64 := BitVec.isLt _
    simp only at h3
    omega_arith
  have outTable := layout.tableApart.disjoint x inWorkspace
  have tableFar : 3456≤ofs table x := by
    change ¬ofs table x+1≤3456 at outTable
    omega_arith
  exact frame x h1 h2 (Or.inr tableFar)

theorem unch_of_low_bytes {base : Addr} {B : Nat} {m m' : Mem}
    (same : ∀d,d<B → m' (off base d)=m (off base d)) : Unch base [(B,2^64)] m m' := by
  intro x hx
  have bound:=hx (B,2^64) (by simp)
  have addrBound : ofs base x<2^64 := BitVec.isLt _
  have low : ofs base x<B := by omega_arith
  have address : off base (ofs base x)=x := by
    dsimp only [off,ofs]
    rw [BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_comm,BitVec.sub_add_cancel]
  simpa only [address] using same (ofs base x) low

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass Spec.Weierstrass
open VG.Impl.Weierstrass.AArch64.P521Native (config buildTable normalizeAndInit)

def nativeFrontArithmetic : Prog isa := .seq buildTable normalizeAndInit

structure NativeArithmeticPost (C : Curve) (base table : Addr) (P : Point C) (k : Nat) (s t : State) : Prop where
  data : WindowData base table k t
  context : NormalizeContext base table 8192 t
  affine : ∀i,i<16 → RepA C (Fin.ofNat C.p (wordsVal t.mem table (216*i) 9))
    (Fin.ofNat C.p (wordsVal t.mem table (216*i+72) 9)) 1 (mul (i+1) P)
  accumulatorX : wordsVal t.mem base 1072 9=0
  accumulatorY : wordsVal t.mem base 1144 9=1
  accumulatorZ : wordsVal t.mem base 1216 9=0
  counter : t.gpr .x19=105
  outputPointer : t.gpr .x20=s.gpr .x20
  sp : t.sp=s.sp
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  vector31 : t.v .v31=s.v .v31
  lowMemory : ∀d,d<856 → t.mem (off base d)=s.mem (off base d)
  originalD : wordsVal t.mem base 2368 9=wordsVal s.mem base 2368 9
  flag : word t.mem base 3232=word s.mem base 3232
  tailGP : ∀r∈[Reg.x27,Reg.x28,Reg.x30],t.gpr r=s.gpr r
  farMemory : ∀x,8192≤ofs base x → 3456≤ofs table x → t.mem x=s.mem x

theorem native_front_arithmetic_ok {C : Curve} (hp : C.p=fieldPrime) (law : Law C) (ha : AM3 C)
    (order : PrimeOrder C) (hc : VG.Proof.Ecdsa.AArch64.BaseCfgOk config)
    {P : Point C} (oncurve : onCurve C P=true) (pne : P≠.infinity) (orderBound : 17≤C.n)
    {base table : Addr} {k : Nat} {s : State} (layout : NormalizeLayout base table 8192)
    (ctx : NormalizeContext base table 8192 s) (tableRegion : (⟨table,3456⟩ : Region)∈s.rd++s.wr)
    (px : wordsVal s.mem base 2800 9<fieldPrime) (py : wordsVal s.mem base 3160 9<fieldPrime)
    (peer : peerPoint C s.mem base=P) (one : wordsVal s.mem base 424 9=1)
    (zero : wordsVal s.mem base 280 9=0) (modulus : ModOkA config.MP' 8192 config.C.p s.mem base)
    (bits : ∀j,j<640 → s.mem (off base (3304+j))=if k.testBit j then 1 else 0) :
    WP isa nativeFrontArithmetic s fun t => NativeArithmeticPost C base table P k s t := by
  rw [nativeFrontArithmetic,WP.seq_iff]
  apply build_initial_loop_wp.mpr
  rw [WP.seq_iff]
  refine WP.mono (build_initial_with_frame hp law ha layout ctx px py peer oncurve one)
    fun a ⟨ia,fa,sa,ra,wa,va,ga,stash⟩ => ?_
  have fwa:=fa.workspace_unch layout
  refine WP.mono (build_loop_ok hp law ha order oncurve pne orderBound layout ia)
    fun b ⟨ib,fb,sb,rb,wb,vb,gb⟩ => ?_
  have fwb:=fb.workspace_unch layout
  have modA : ModOkA config.MP' 8192 config.C.p a.mem base :=
    {modulus with val:=by rw [fwa.wordsVal (by decide) (by decide)]; exact modulus.val}
  have modB : ModOkA config.MP' 8192 config.C.p b.mem base :=
    {modA with val:=by rw [fwb.wordsVal (by decide) (by decide)]; exact modA.val}
  apply normalize_phases_machine_wp.mpr
  refine WP.mono (normalize_phases_ok hc layout ib.normalize_start ib.context.tableW modB)
    fun t normal => ?_
  have low (d : Nat) (hd : d<856) : t.mem (off base d)=s.mem (off base d) := by
    rw [normal.lowMemory d hd,fwb.byte (d:=d) (by
      intro w hw; simp only [buildLoopWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl|rfl <;> exact Or.inl (by omega_arith)) (by omega_arith),
      fwa.byte (d:=d) (by
        intro w hw; simp only [buildInitialWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
        rcases hw with rfl|rfl|rfl <;> exact Or.inl (by omega_arith)) (by omega_arith)]
  have lowFrame:=unch_of_low_bytes low
  have readonly (d : Nat) (lo : 3232≤d) (hi : d<3944) : t.mem (off base d)=s.mem (off base d) := by
    rw [normal.readonly d lo (by omega_arith),
      fwb.byte (d:=d) (by
        intro w hw; simp only [buildLoopWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
        rcases hw with rfl|rfl|rfl <;> simp only <;> omega_arith) (by omega_arith),
      fwa.byte (d:=d) (by
        intro w hw; simp only [buildInitialWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
        rcases hw with rfl|rfl|rfl <;> simp only <;> omega_arith) (by omega_arith)]
  have data : WindowData base table k t := by
    refine ⟨normal.context.workspace,?_,?_,?_,?_⟩
    · refine ⟨normal.context.readTable.reg,?_⟩
      intro d hd
      exact ⟨⟨table,3456⟩,by rw [normal.rd,normal.wr,rb,wb,ra,wa]; exact tableRegion,
        VG.Offset.contains_base table hd (by omega_arith)⟩
    · intro d lo hi
      have bx:=normal.tableValues.canonical (d-1) (by omega_arith) 0 (by decide)
      have byY:=normal.tableValues.canonical (d-1) (by omega_arith) 1 (by decide)
      exact ⟨bx,byY⟩
    · rw [lowFrame.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)]
      exact zero
    · intro j hj
      rw [readonly (3304+j) (by omega_arith) (by omega_arith)]
      exact bits j (by omega_arith)
  refine ⟨data,normal.context,native_front_table_affine hp law order oncurve pne orderBound ib normal,
    normal.accumulatorX,normal.accumulatorY,normal.accumulatorZ,normal.counter,?_,
    normal.sp.trans (sb.trans sa),normal.rd.trans (rb.trans ra),normal.wr.trans (wb.trans wa),
    normal.vector31.trans (vb.trans va),low,?_,?_,?_,?_⟩
  · rw [normal.outputPointer,fwb.word (d:=3944) (by decide) (by decide),stash]
  · rw [normal.originalD,fwb.wordsVal (d:=2368) (k:=9) (by decide) (by decide),
      fwa.wordsVal (d:=2368) (k:=9) (by decide) (by decide)]
  · apply Mem.readW_congr
    intro i hi
    have address : off base 3232+BitVec.ofNat 64 i=off base (3232+i) := VG.Offset.add_ofNat_add_ofNat base 3232 i
    rw [address]
    exact readonly (3232+i) (by omega_arith) (by omega_arith)
  · intro r hr
    have choices : r=Reg.x27 ∨ r=Reg.x28 ∨ r=Reg.x30 := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hr
    rcases choices with rfl|rfl|rfl
    · exact (normal.tailGP _ (by decide)).trans ((gb _ (by decide)).trans (ga _ (by decide)))
    · exact (normal.tailGP _ (by decide)).trans ((gb _ (by decide)).trans (ga _ (by decide)))
    · exact normal.link.trans ((gb _ (by decide)).trans (ga _ (by decide)))
  · intro x workspaceFar tableFar
    have first:=fa x (Or.inr (by omega_arith)) (Or.inr (by omega_arith)) (Or.inr (by omega_arith))
    have second:=fb x (Or.inr (by omega_arith)) (Or.inr (by omega_arith)) (Or.inr tableFar)
    exact (normal.farMemory x workspaceFar tableFar).trans (second.trans first)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass Spec.Weierstrass
open VG.Impl.Weierstrass.AArch64.P521Native (config recodeScalar)

def nativeRecodeArithmetic : Prog isa := .seq recodeScalar nativeFrontArithmetic

private theorem recode_v31 {s : State} {Q : State → Prop} (h : WP isa recodeScalar s Q) :
    WP isa recodeScalar s fun t => Q t ∧ t.v .v31=s.v .v31 := by
  obtain ⟨trace,t,exec,q⟩:=h
  exact ⟨trace,t,exec,q,Exec.vec (c:=recodeScalar) (r:=.v31) (by decide) exec⟩

theorem native_recode_arithmetic_ok {C : Curve} (hp : C.p=fieldPrime) (law : Law C) (ha : AM3 C)
    (order : PrimeOrder C) (hc : VG.Proof.Ecdsa.AArch64.BaseCfgOk config)
    {P : Point C} (oncurve : onCurve C P=true) (pne : P≠.infinity) (orderBound : 17≤C.n)
    {base table : Addr} {s : State} (layout : NormalizeLayout base table 8192)
    (ctx : NormalizeContext base table 8192 s) (tableRegion : (⟨table,3456⟩ : Region)∈s.rd++s.wr)
    (px : wordsVal s.mem base 2800 9<fieldPrime) (py : wordsVal s.mem base 3160 9<fieldPrime)
    (peer : peerPoint C s.mem base=P) (one : wordsVal s.mem base 424 9=1)
    (zero : wordsVal s.mem base 280 9=0) (modulus : ModOkA config.MP' 8192 config.C.p s.mem base)
    (counter : s.gpr .x19=80) (bitOne : s.gpr .x5=1) :
    WP isa nativeRecodeArithmetic s fun t => NativeArithmeticPost C base table P
      (wordsVal s.mem base 3944 10) s t := by
  rw [nativeRecodeArithmetic,WP.seq_iff]
  refine WP.mono (recode_v31 (recode_scalar_ok ctx.workspace counter bitOne))
    fun u ⟨⟨bits,ku,fu,_⟩,vu⟩ => ?_
  have ctxU : NormalizeContext base table 8192 u :=
    ⟨ctx.workspace.of_keepRegs ku (by decide),ctx.readTable.of_keepRegs ku (by decide),ctx.tableW.of_keepRegs ku (by decide)⟩
  have same (d : Nat) (fit : d+72≤3304) : wordsVal u.mem base d 9=wordsVal s.mem base d 9 :=
    fu.wordsVal (Or.inl fit) (by omega_arith)
  have peerU : peerPoint C u.mem base=P := by
    simpa only [peerPoint,same 2800 (by decide),same 3160 (by decide)] using peer
  have modU : ModOkA config.MP' 8192 config.C.p u.mem base :=
    {modulus with val:=by rw [fu.wordsVal (by decide) (by decide)]; exact modulus.val}
  refine WP.mono (native_front_arithmetic_ok hp law ha order hc oncurve pne orderBound layout ctxU
    (by rw [ku.rd,ku.wr]; exact tableRegion)
    (by rw [same 2800 (by decide)]; exact px) (by rw [same 3160 (by decide)]; exact py) peerU
    (by rw [same 424 (by decide)]; exact one) (by rw [same 280 (by decide)]; exact zero) modU bits)
    fun t post => ?_
  refine ⟨post.data,post.context,post.affine,post.accumulatorX,post.accumulatorY,post.accumulatorZ,post.counter,
    post.outputPointer.trans (ku.gpr .x20 (by decide)),post.sp.trans ku.sp,post.rd.trans ku.rd,post.wr.trans ku.wr,
    post.vector31.trans vu,?_,?_,?_,?_,?_⟩
  · intro d hd
    rw [post.lowMemory d hd]
    apply fu
    rw [ofs_off0 base (by omega_arith)]
    exact Or.inl (by omega_arith)
  · rw [post.originalD,same 2368 (by decide)]
  · rw [post.flag,fu.word (d:=3232) (Or.inl (by decide)) (by decide)]
  · intro r hr
    have choices : r=Reg.x27 ∨ r=Reg.x28 ∨ r=Reg.x30 := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hr
    rcases choices with rfl|rfl|rfl
    all_goals exact (post.tailGP _ (by decide)).trans (ku.gpr _ (by decide))
  · intro x workspaceFar tableFar
    exact (post.farMemory x workspaceFar tableFar).trans (fu x (Or.inr (by omega_arith)))

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass Spec.Weierstrass VG.Proof.Ecdsa.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config validateAndPrepare)
open VG.Proof.Ed25519.AArch64 (Keeps)

def nativeFront : Prog isa := .seq validateAndPrepare nativeRecodeArithmetic

def NativeApiFrontPost (s t : State) : Prop :=
  ∃ args loaded ready, ∃ P : Point config.C,
    Keeps [.x2,.x3,.x4,.x6,.x26] (allocated 3456 s) args ∧
    St₁ config none args (s.gpr .x3) loaded ∧
    PrepareCorePost args loaded (s.gpr .x3) (s.gpr .x2) ready ∧
    onCurve config.C P=true ∧ P≠.infinity ∧
    wordsVal ready.mem (s.gpr .x3) 3944 10<32^105 ∧
    NativeArithmeticPost config.C (s.gpr .x3) (s.sp-3456#64) P
      (wordsVal ready.mem (s.gpr .x3) 3944 10) ready t ∧
    t.gpr .x20=s.gpr .x0 ∧ t.sp=(allocated 3456 s).sp ∧ t.v .v31=s.v .v31 ∧
    t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧
    t.rd=(allocated 3456 s).rd ∧ t.wr=(allocated 3456 s).wr ∧
    (∀x,8192≤ofs (s.gpr .x3) x → 3456≤ofs (s.sp-3456#64) x → t.mem x=s.mem x) ∧
    args.gpr .x3=s.gpr .x1 ∧ args.gpr .x2=s.gpr .x2+BitVec.ofNat 64 1 ∧
    peerPoint config.C ready.mem (s.gpr .x3)=P

private theorem native_prime : config.C.p=fieldPrime := by
  dsimp only [config,VG.Impl.Ecdsa.AArch64.p521,Spec.P521.curve,Spec.P521.p,fieldPrime]

theorem native_front_api_ok (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) (orderBound : 17≤config.C.n) {s : State} (pre : PrepareStackPre s) :
    WP isa nativeFront (allocated 3456 s) fun t => NativeApiFrontPost s t := by
  rw [nativeFront,WP.seq_iff]
  refine WP.mono (prepare_preserved (prepare_api_ready hc pre.allocatedArgs))
    fun ready ⟨⟨args,loaded,keep,argTable,_,privateArg,stage,post,peerPlus⟩,rsp,rv31,r27,r28⟩ => ?_
  have postOriginal:=post
  obtain ⟨P,oncurve,pne,peer,px,py,one,zero,_,modulus,_,_⟩ := prepare_selected_ready hc stage post
  obtain ⟨_,_,_,scr,_,_,kBound,_,counter,bitOne,g20,g26,_,_,_,rd,wr,frame,_,_⟩:=post
  have tableReg : ready.gpr .x26=s.sp-3456#64 :=
    g26.trans ((stage.gpr .x26 (by decide)).trans argTable)
  have tableWr : ready.wr=(allocated 3456 s).wr := wr.trans (stage.wr.trans keep.wr)
  have ctx : NormalizeContext (s.gpr .x3) (s.sp-3456#64) 8192 ready :=
    ⟨scr,pre.tablePtr tableReg tableWr,pre.tablePtrW tableReg tableWr⟩
  have layout : NormalizeLayout (s.gpr .x3) (s.sp-3456#64) 8192 := ⟨by decide,by decide,pre.tableApart⟩
  have tableRegion : (⟨s.sp-3456#64,3456⟩ : Region)∈ready.rd++ready.wr := by
    apply List.mem_append_right
    rw [tableWr]
    simp [allocated]
  refine WP.mono (native_recode_arithmetic_ok native_prime law ha order hc oncurve pne orderBound layout ctx
    tableRegion px py peer one zero modulus counter bitOne) fun t result => ?_
  refine ⟨args,loaded,ready,P,keep,stage,postOriginal,oncurve,pne,kBound,result,?_,
    result.sp.trans rsp,result.vector31.trans rv31,
    (result.tailGP .x27 (by decide)).trans r27,(result.tailGP .x28 (by decide)).trans r28,
    result.rd.trans (rd.trans (stage.rd.trans keep.rd)),result.wr.trans tableWr,?_,privateArg,peerPlus,peer⟩
  · exact result.outputPointer.trans (g20.trans (stage.x20.trans (keep.gpr .x0 (by decide))))
  · intro x workspaceFar tableFar
    have readySame:=frame.far (x:=x) (by
      intro w hw
      have fits : ∀w∈prepareCoreWrites,w.1+w.2≤8192 := by decide
      have fit:=fits w hw
      exact Nat.le_trans fit workspaceFar)
    have loadedSame:=stage.unch.far (x:=x) (by
      intro w hw
      rw [List.mem_singleton.mp hw]
      exact workspaceFar)
    exact (result.farMemory x workspaceFar tableFar).trans (readySame.trans (loadedSame.trans (congrFun keep.mem x)))

end VG.Proof.Weierstrass.AArch64.P521Native
