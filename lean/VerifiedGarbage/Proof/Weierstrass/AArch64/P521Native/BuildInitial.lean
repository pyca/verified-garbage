module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildSeedStore
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildCounter
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildLoopTransfer
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

-- separate module: Initial table seeding, exact doubling and ABI/frame composition cost 0.64s of proof checking versus 0.37s imports in the recorded M1 profile; keeping this phase checked independently avoids replay for front-end wiring edits.

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

def buildSeedPointer : List Instr := [.addImm .x .x20 .x26 216]
def buildSeedCounter : List Instr := [.addImm .x .x20 .x20 216,.movz .x .x19 14 0]

theorem build_seed_tail_source : outerBlock015.drop 283=buildSeedPointer ++
    (buildStoreCopy .x20 27 1288 0 ++ (buildCopyPoint ++ buildSeedCounter)) := by lit_decide

theorem build_seed_pointer_ok (s : State) :
    WP isa (.block buildSeedPointer) s fun t =>
      t.gpr .x20=s.gpr .x26+216#64 ∧ Keeps [.x20] s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [buildSeedPointer,runBlock_cons,runStep_some,runBlock_nil,reduceExec,Size.bits,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.v_write,BitVec.setWidth_eq,ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,⟨?_,by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩,trivial⟩
  reg_keeps

theorem build_seed_counter_ok (s : State) :
    WP isa (.block buildSeedCounter) s fun t =>
      t.gpr .x20=s.gpr .x20+216#64 ∧ t.gpr .x19=14#64 ∧
      Keeps [.x20,.x19] s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [buildSeedCounter,runBlock_cons,runStep_some,runBlock_nil,reduceExec,Size.bits,
    Nat.reduceLT,Nat.reduceMul,RegUpd.gpr_write,RegUpd.v_write,BitVec.setWidth_eq,reduceCtorEq,
    ite_true,ite_false,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,⟨?_,by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩,trivial⟩
  reg_keeps

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Impl.Weierstrass.AArch64.P521Native

def buildSeed : Prog isa := .seq (.block [.str .x .x20 .x0 3944]) (.block buildSeedStore)

theorem build_seed_source : outerBlock007.take 55=[.str .x .x20 .x0 3944]++buildSeedStore := by lit_decide

theorem build_seed_ok {base table : Addr} {s : State}
    (hs : Scr s base 8192) (pt : PtrW s .x26 table 216)
    (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,216⟩) :
    WP isa buildSeed s fun t =>
      wordsVal t.mem table 0 9=wordsVal s.mem base 2800 9 ∧
      wordsVal t.mem table 72 9=wordsVal s.mem base 3160 9 ∧
      wordsVal t.mem table 144 9=wordsVal s.mem base 424 9 ∧
      word t.mem base 3944=s.gpr .x20 ∧
      KeepRegs [.x1] s t ∧ Unch base [(3944,8),(8192,2^64)] s.mem t.mem ∧
      (∀x,(ofs base x<3944 ∨ 3952≤ofs base x) → (ofs table x<0 ∨ 216≤ofs table x) → t.mem x=s.mem x) := by
  rw [buildSeed,WP.seq_iff]
  refine WP.mono (stR_ok hs.ptrW (d:=3944) (by decide) (by decide) .x20) fun u eu => ?_
  have ku : KeepRegs [.x1] s u := by
    rw [eu]
    exact ⟨fun _ _ => rfl,rfl,rfl,rfl⟩
  have hu := hs.of_keepRegs ku (by decide)
  have pu := pt.of_keepRegs ku (by decide)
  have fu : Outside base 3944 8 s.mem u.mem := by
    rw [eu]
    exact writeW_outside _ _ _ (by decide)
  have saved : word u.mem base 3944=s.gpr .x20 := by rw [eu,word_writeW_self]
  refine WP.mono (build_seed_store_ok hu pu apart) fun t ⟨xt,yt,zt,kt,ft⟩ => ?_
  have wt := ft.unch_far apart
  refine ⟨?_,?_,?_,?_,ku.trans kt,?_,?_⟩
  · rw [xt]; exact fu.wordsVal (Or.inl (by decide)) (by decide)
  · rw [yt]; exact fu.wordsVal (Or.inl (by decide)) (by decide)
  · rw [zt]; exact fu.wordsVal (Or.inl (by decide)) (by decide)
  · rw [wt.word (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide),saved]
  · exact fu.unch.trans wt
  · intro x hw ht
    exact (ft x ht).trans (fu x hw)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass

def buildSeedTail : Prog isa := .seq (.block buildSeedPointer) (.seq buildAdvance (.block buildSeedCounter))

theorem build_seed_tail_ok {base table : Addr} {s : State}
    (hs : Scr s base 8192) (pt : PtrW s .x26 table 3456)
    (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩) :
    WP isa buildSeedTail s fun t =>
      (∀c,c<3 → wordsVal t.mem table (216+72*c) 9=wordsVal s.mem base (1288+72*c) 9) ∧
      (∀c,c<3 → wordsVal t.mem base (1504+72*c) 9=wordsVal s.mem base (1288+72*c) 9) ∧
      t.gpr .x20=off table 432 ∧ t.gpr .x19=14#64 ∧
      KeepRegs [.x1,.x19,.x20] s t ∧
      Unch base [(1504,72),(1576,72),(1648,72),(8192,2^64)] s.mem t.mem ∧
      BuildLoopFrame base table 1 216 s.mem t.mem := by
  rw [buildSeedTail,WP.seq_iff]
  refine WP.mono (build_seed_pointer_ok s) fun u ⟨gu,ku,vu⟩ => ?_
  have hu := hs.of_keepRegs (Keeps.regs ku) (by decide)
  have pu := pt.of_keepRegs (Keeps.regs ku) (by decide)
  have g20 : u.gpr .x20=off table 216 := by rw [gu,pt.reg]
  have piece := build_output_ptr pu (e:=216) (by decide) g20
  have pieceApart := build_output_apart apart (e:=216) (by decide)
  rw [WP.seq_iff]
  refine WP.mono (build_advance_ok hu piece pieceApart) fun v ⟨tv,ev,kv,cross,fv⟩ => ?_
  refine WP.mono (build_seed_counter_ok v) fun t ⟨gt,ct,kt,_⟩ => ?_
  have regs : KeepRegs [.x1,.x19,.x20] s t := by
    refine ⟨?_,kt.rd.trans (kv.rd.trans ku.rd),kt.wr.trans (kv.wr.trans ku.wr),kt.sp.trans (kv.sp.trans ku.sp)⟩
    intro r hr
    have h1 : r≠.x1 := by intro e; subst r; exact hr (by simp)
    have h19 : r≠.x19 := by intro e; subst r; exact hr (by simp)
    have h20 : r≠.x20 := by intro e; subst r; exact hr (by simp)
    exact (kt.gpr r (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact ⟨h20,h19⟩)).trans
      ((kv.gpr r (by simpa only [List.mem_singleton] using h1)).trans
        (ku.gpr r (by simpa only [List.mem_singleton] using h20)))
  refine ⟨?_,?_,?_,ct,regs,?_,?_⟩
  · intro c hc
    rw [kt.mem,←VG.Proof.Weierstrass.AArch64.Mont.wordsVal_off v.mem table 216 (72*c) 9,tv c hc,ku.mem]
  · intro c hc
    rw [kt.mem,ev c hc,ku.mem]
  · rw [gt,kv.gpr .x20 (by decide),g20]
    exact build_counter_pointer (m:=1)
  · rw [kt.mem,←ku.mem]
    exact fv

  · have frame := BuildLoopFrame.of_advance (row:=1) (by decide) cross fv
    rw [kt.mem,←ku.mem]
    exact frame

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass Spec.Weierstrass

def buildInitial : Prog isa := .seq buildSeed (.seq buildDoubleMachine buildSeedTail)

def BuildInitialFrame (base table : Addr) (m m' : Mem) : Prop :=
  ∀x,(ofs base x<1288 ∨ 2152≤ofs base x) → (ofs base x<3944 ∨ 4024≤ofs base x) →
    (ofs table x<0 ∨ 432≤ofs table x) → m' x=m x

private theorem seed_v31 {s : State} {Q : State → Prop} (h : WP isa buildSeed s Q) :
    WP isa buildSeed s fun t => Q t ∧ t.v .v31=s.v .v31 := by
  obtain ⟨trace,t,exec,q⟩:=h
  exact ⟨trace,t,exec,q,Exec.vec (c:=buildSeed) (r:=.v31) (by decide) exec⟩

private theorem seed_tail_v31 {s : State} {Q : State → Prop} (h : WP isa buildSeedTail s Q) :
    WP isa buildSeedTail s fun t => Q t ∧ t.v .v31=s.v .v31 := by
  obtain ⟨trace,t,exec,q⟩:=h
  exact ⟨trace,t,exec,q,Exec.vec (c:=buildSeedTail) (r:=.v31) (by decide) exec⟩

theorem build_initial_with_frame {C : Curve} (hp : C.p=fieldPrime) (law : Law C) (ha : AM3 C)
    {base table : Addr} {s : State} {P : Point C}
    (layout : NormalizeLayout base table 8192) (ctx : NormalizeContext base table 8192 s)
    (px : wordsVal s.mem base 2800 9<fieldPrime) (py : wordsVal s.mem base 3160 9<fieldPrime)
    (peer : peerPoint C s.mem base=P) (hP : onCurve C P=true)
    (one : wordsVal s.mem base 424 9=1) :
    WP isa buildInitial s fun t => BuildLoopInv C base table P 2 t ∧
      BuildInitialFrame base table s.mem t.mem ∧ t.sp=s.sp ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      t.v .v31=s.v .v31 ∧ (∀r∈[Reg.x26,.x27,.x28,.x30],t.gpr r=s.gpr r) ∧ word t.mem base 3944=s.gpr .x20 := by
  have primeOne : 1<fieldPrime := by
    dsimp only [fieldPrime]
    rw [VG.Proof.Mont.AArch64.P521Square.prime_value]
    decide
  have apart := layout.tableApart.disjoint
  have piece : PtrW s .x26 table 216 :=
    ⟨ctx.tableW.reg,fun d hd => ctx.tableW.st d (by omega_arith),by decide,by have h:=ctx.tableW.nowrap; omega_arith⟩
  have pieceApart := apart.sub_right (VG.Offset.sub_base table (d:=0) (by decide : 0+216≤3456))
  have pieceApart' : Region.Disjoint ⟨base,8192⟩ ⟨table,216⟩ := by simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using pieceApart
  rw [buildInitial,WP.seq_iff]
  refine WP.mono (seed_v31 (build_seed_ok ctx.workspace piece pieceApart')) fun u ⟨⟨x0,y0,z0,stash,ku,fu,seedCross⟩,seedV⟩ => ?_
  have hu := ctx.workspace.of_keepRegs ku (by decide)
  have pwu := ctx.tableW.of_keepRegs ku (by decide)
  have pru := ctx.readTable.of_keepRegs ku (by decide)
  have usame (d : Nat) (hd : d+72≤3944) : wordsVal u.mem base d 9=wordsVal s.mem base d 9 :=
    fu.wordsVal (by intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw; rcases hw with rfl|rfl <;> exact Or.inl (by omega_arith)) (by omega_arith)
  have uone : wordsVal u.mem base 424 9=1 := (usame 424 (by decide)).trans one
  have upx : wordsVal u.mem base 2800 9<fieldPrime := by rw [usame 2800 (by decide)]; exact px
  have upy : wordsVal u.mem base 3160 9<fieldPrime := by rw [usame 3160 (by decide)]; exact py
  have upeer : peerPoint C u.mem base=P := by simpa only [peerPoint,usame 2800 (by decide),usame 3160 (by decide)] using peer
  have start : InvJ C (Fin.ofNat C.p (wordsVal u.mem base 2800 9))
      (Fin.ofNat C.p (wordsVal u.mem base 3160 9)) (Fin.ofNat C.p (wordsVal u.mem base 424 9)) P := by
    rw [uone,←upeer]
    exact InvJ.affine law _ _
  rw [WP.seq_iff]
  refine WP.mono (build_double_group hp law ha hu (by decide) (by decide) upx upy
    (by rw [uone]; exact primeOne) hP start) fun v ⟨dv,jv,hv,pv,fv⟩ => ?_
  have fieldFrame := build_double_frame fv
  have fieldOutside : Outside base 0 8192 u.mem v.mem := fieldFrame.unch.outside (by decide)
  have vsame (d : Nat) (hd : d+72≤1288 ∨ (2152≤d ∧ d+72≤3952)) :
      wordsVal v.mem base d 9=wordsVal u.mem base d 9 :=
    fieldFrame.readonly d 9 (by omega_arith) (by omega_arith)
  have tableSame (d : Nat) (hd : d+72≤3456) : wordsVal v.mem table d 9=wordsVal u.mem table d 9 :=
    layout.tableApart.wordsVal fieldOutside 9 d (by omega_arith)
  have pvw : PtrW v .x26 table 3456 :=
    ⟨(pv.gpr .x26 (by decide)).trans pwu.reg,by rw [pv.wr]; exact pwu.st,pwu.enc,pwu.nowrap⟩
  refine WP.mono (seed_tail_v31 (build_seed_tail_ok hv pvw apart)) fun t ⟨⟨trow,ecur,ptr,count,kt,_,ft⟩,tailV⟩ => ?_
  have ht := hv.of_keepRegs kt (by decide)
  have ctxT : NormalizeContext base table 8192 t :=
    ⟨ht,⟨(kt.gpr .x26 (by decide)).trans ((pv.gpr .x26 (by decide)).trans pru.reg),
      by rw [kt.rd,kt.wr,pv.rd,pv.wr]; exact pru.ld,pru.enc⟩,
      pvw.of_keepRegs kt (by decide)⟩
  have tsame (d : Nat) (hd : d+72≤1288 ∨ (2152≤d ∧ d+72≤3944)) : wordsVal t.mem base d 9=wordsVal s.mem base d 9 := by
    rw [ft.workspace_words layout.tableApart (by decide) (by decide) 9 d (by omega_arith)
      (by omega_arith) (by omega_arith),vsame d (by omega_arith),usame d (by omega_arith)]
  have first (c : Nat) (hc : c<3) : wordsVal t.mem table (72*c) 9=wordsVal s.mem base (if c=0 then 2800 else if c=1 then 3160 else 424) 9 := by
    rw [ft.table_words layout.tableApart (by decide) 9 (72*c) (by omega_arith) (Or.inl (by omega_arith)),tableSame _ (by omega_arith)]
    have cases : c=0 ∨ c=1 ∨ c=2 := by omega_arith
    rcases cases with rfl|rfl|rfl
    · exact x0
    · exact y0
    · exact z0
  have currentPoint := pointAt_copy (C:=C) ecur
  have rowPoint := pointAt_copy (C:=C) trow
  have two : Spec.Weierstrass.add P P=mul 2 P := by
    calc
      Spec.Weierstrass.add P P=Spec.Weierstrass.add (mul 1 P) (mul 1 P) := by rw [mul_one_pt]
      _=mul (1+1) P := law.add_mul_mul hP 1 1
  have ready : BuildLoopInv C base table P 2 t := by
    refine ⟨ctxT,ptr,count,by rw [tsame 2800 (by decide)]; exact px,
      by rw [tsame 3160 (by decide)]; exact py,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [peerPoint,tsame 2800 (by decide),tsame 3160 (by decide)] using peer
    · have eq := ecur
      exact ⟨by rw [eq 0 (by decide)]; exact dv.1,
        by rw [eq 1 (by decide)]; exact dv.2.1,by rw [eq 2 (by decide)]; exact dv.2.2⟩
    · rw [currentPoint,←two]; exact jv
    · intro i hi c hc
      have ci : c=0 ∨ c=1 ∨ c=2 := by omega_arith
      have ii : i=0 ∨ i=1 := by omega_arith
      rcases ii with rfl|rfl
      · rw [show 216*0+72*c=72*c by omega_arith,first c hc]
        rcases ci with rfl|rfl|rfl
        · exact px
        · exact py
        · change wordsVal s.mem base 424 9<fieldPrime
          rw [one]; exact primeOne
      · rw [show 216*1+72*c=216+72*c by omega_arith,trow c hc]
        rcases ci with rfl|rfl|rfl
        · exact dv.1
        · exact dv.2.1
        · exact dv.2.2
    · intro i hi
      have ii : i=0 ∨ i=1 := by omega_arith
      rcases ii with rfl|rfl
      · simp only [Nat.zero_add,mul_one_pt]
        have fx:=first 0 (by decide)
        have fy:=first 1 (by decide)
        have fz:=first 2 (by decide)
        simp only [pointAt,Nat.mul_zero,Nat.zero_add,Nat.mul_one,Nat.reduceMul] at fx fy fz ⊢
        rw [fx,fy,fz]
        simp only [reduceCtorEq,show ¬(2=1) from by decide,ite_true,ite_false]
        rw [one,←peer]
        exact InvJ.affine law _ _
      · rw [show 216*1=216 from rfl,rowPoint,←two]; exact jv
    · have hz:=first 2 (by decide)
      exact hz.trans one
    · exact tsame 424 (by decide) |>.trans one
  refine ⟨ready,?_,kt.sp.trans (pv.sp.trans ku.sp),kt.rd.trans (pv.rd.trans ku.rd),
    kt.wr.trans (pv.wr.trans ku.wr),tailV.trans (pv.v31.trans seedV),?_,?_⟩
  · intro x hw hs ht
    exact (ft x hw (by omega_arith) (by omega_arith)).trans
      ((fieldFrame x hw (by omega_arith)).trans (seedCross x (by omega_arith) (by omega_arith)))
  · intro r hr
    have rr : r∈[Reg.x26,.x27,.x28,.x30] := hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at rr
    rcases rr with rfl|rfl|rfl|rfl
    all_goals exact (kt.gpr _ (by decide)).trans ((pv.gpr _ (by decide)).trans (ku.gpr _ (by decide)))
  · have e := ft.workspace_words layout.tableApart (by decide) (by decide) 1 3944
      (by decide) (Or.inr (by decide)) (Or.inl (by decide))
    simp only [wordsVal,Nat.mul_zero,Nat.add_zero] at e
    have we : word t.mem base 3944=word v.mem base 3944 := BitVec.eq_of_toNat_eq e
    rw [we,fieldFrame.unch.word (by decide) (by decide),stash]

 theorem build_initial_ok {C : Curve} (hp : C.p=fieldPrime) (law : Law C) (ha : AM3 C)
    {base table : Addr} {s : State} {P : Point C}
    (layout : NormalizeLayout base table 8192) (ctx : NormalizeContext base table 8192 s)
    (px : wordsVal s.mem base 2800 9<fieldPrime) (py : wordsVal s.mem base 3160 9<fieldPrime)
    (peer : peerPoint C s.mem base=P) (hP : onCurve C P=true)
    (one : wordsVal s.mem base 424 9=1) :
    WP isa buildInitial s (BuildLoopInv C base table P 2) :=
  WP.mono (build_initial_with_frame hp law ha layout ctx px py peer hP one) (fun _ h => h.1)

end VG.Proof.Weierstrass.AArch64.P521Native
