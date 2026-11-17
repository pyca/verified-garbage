module

import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleFunction
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.OuterBlocks
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! ### `Weierstrass.AArch64.P521Native.WindowDoubleStep`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native (callNormalDouble)
open VG.Proof.Weierstrass (dblJF)

def windowDoubleK (W a o : Nat) (base : Addr) (mem : Mem) : Contract isa where
  pre t := DoublePre t W a o ∧ t.gpr .x0=base ∧ t.mem=mem
  post s t := canonicalPoint t.mem base o ∧
    ordinaryPoint t.mem base o=dblJF (ordinaryPoint mem base a).1
      (ordinaryPoint mem base a).2.1 (ordinaryPoint mem base a).2.2 ∧
    DoubleFrame base o mem t.mem ∧ t.gpr .x0=base ∧ t.v .v29=s.v .v29 ∧ t.v .v31=s.v .v31
  pub _ _ := True

theorem window_double_call_ok {s : State} {W a o : Nat} (hp : DoublePre s W a o)
    (ha : canonicalPoint s.mem (s.gpr .x0) a) :
    WP isa callNormalDouble s fun t =>
      canonicalPoint t.mem (s.gpr .x0) o ∧
      ordinaryPoint t.mem (s.gpr .x0) o=dblJF (ordinaryPoint s.mem (s.gpr .x0) a).1
        (ordinaryPoint s.mem (s.gpr .x0) a).2.1 (ordinaryPoint s.mem (s.gpr .x0) a).2.2 ∧
      DoubleFrame (s.gpr .x0) o s.mem t.mem ∧ t.gpr .x0=s.gpr .x0 ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      (∀r∈preserved,r≠.x30 → t.gpr r=s.gpr r) ∧ t.v .v29=s.v .v29 ∧ t.v .v31=s.v .v31 := by
  let base := s.gpr .x0
  have hcov : Covers [⟨base,W⟩] s.wr := by
    exact Covers.one ⟨_,hp.workspace.wr,by
      have h := hp.workspace.contains (d:=0) (n:=W) (by omega_arith) (by have hmin:=hp.room; omega_arith)
      simpa [off] using h⟩
  let entry := s.callEntry.withRegions [] [⟨base,W⟩]
  have ce (r : Reg) (hr : r∉linkRegs) : entry.gpr r=s.gpr r := State.callEntry_gpr s hr
  have e0 : entry.gpr .x0=base := ce .x0 (by decide)
  have ws : Scr entry (entry.gpr .x0) W := by
    refine ⟨rfl,?_,?_,hp.workspace.enc⟩
    · rw [e0]; exact List.mem_cons_self
    · rw [e0]; exact hp.workspace.nowrap
  have pre : DoublePre entry W a o :=
    ⟨ws,hp.room,hp.layout,(ce .x1 (by decide)).trans hp.argO,(ce .x2 (by decide)).trans hp.argA⟩
  apply WP.callV (k:=windowDoubleK W a o base s.mem)
    (fun t ⟨pt,t0,mt⟩ => ?_)
    (rd:=[]) (wr:=[⟨base,W⟩]) ⟨pre,e0,rfl⟩ (Covers.right hcov) hcov
    (fun t rd wr sp _ gp _ _ post => ?_) (by rfl)
  · have ht : canonicalPoint t.mem (t.gpr .x0) a := by rw [t0,mt]; exact ha
    obtain ⟨trace,u,exec,abi,b,p,frame,zero,_,_,vec⟩ := double_fn_ok pt ht
    rw [t0] at b
    rw [t0,mt] at p frame
    rw [t0] at zero
    exact ⟨trace,u,exec,abi,b,p,frame,zero,vec .v29 (by decide),vec .v31 (by decide)⟩
  · rcases post with ⟨b,p,frame,zero,v29,v31⟩
    exact ⟨b,p,frame,zero,rd,wr,sp,gp,v29,v31⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

def windowArgs (o a : BitVec 16) : List Instr := [.movz .x .x1 o 0,.movz .x .x2 a 0]

theorem window_args_ok (s : State) (o a : BitVec 16) :
    WP isa (.block (windowArgs o a)) s fun t =>
      t.gpr .x1=o.setWidth 64 ∧ t.gpr .x2=a.setWidth 64 ∧ Keeps [.x1,.x2] s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [windowArgs,runBlock_cons,runStep_some,runBlock_nil,reduceExec,Size.bits,Nat.reduceMul,
    Nat.reduceLT,ite_true,BitVec.shiftLeft_zero,RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_false,
    Option.some.injEq,exists_eq_left']
  refine ⟨trivial,trivial,⟨?_,by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩,rfl⟩
  reg_keeps

theorem window_args_forward (s : State) :
    WP isa (.block outerBlock138) s fun t =>
      t.gpr .x1=1288#64 ∧ t.gpr .x2=1072#64 ∧ Keeps [.x1,.x2] s t ∧ t.v=s.v :=
  window_args_ok s 1288 1072

theorem window_args_backward (s : State) :
    WP isa (.block outerBlock139) s fun t =>
      t.gpr .x1=1072#64 ∧ t.gpr .x2=1288#64 ∧ Keeps [.x1,.x2] s t ∧ t.v=s.v :=
  window_args_ok s 1072 1288

theorem window_args_extra (s : State) :
    WP isa (.block outerBlock141) s fun t =>
      t.gpr .x1=1288#64 ∧ t.gpr .x2=1072#64 ∧ Keeps [.x1,.x2] s t ∧ t.v=s.v :=
  window_args_ok s 1288 1072

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native (callNormalDouble)
open VG.Proof.Weierstrass (dblJF)

structure WindowStable (s t : State) : Prop where
  base : t.gpr .x0=s.gpr .x0
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  gp : ∀r∈preserved,r≠.x30 → t.gpr r=s.gpr r
  v29 : t.v .v29=s.v .v29
  v31 : t.v .v31=s.v .v31

 theorem WindowStable.trans {s t u : State} (h : WindowStable s t) (k : WindowStable t u) : WindowStable s u :=
  ⟨k.base.trans h.base,k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp,
    fun r hr hn => (k.gp r hr hn).trans (h.gp r hr hn),k.v29.trans h.v29,k.v31.trans h.v31⟩

 theorem WindowStable.scr {s t : State} {W : Nat} (h : WindowStable s t) (hs : Scr s (s.gpr .x0) W) :
    Scr t (t.gpr .x0) W := by
  refine ⟨rfl,?_,?_,hs.enc⟩
  · rw [h.base,h.wr]; exact hs.wr
  · rw [h.base]; exact hs.nowrap

 theorem window_double_step_ok {s : State} {W a o : Nat} {args : List Instr}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W) (layout : DoubleLayout a o)
    (ha : canonicalPoint s.mem (s.gpr .x0) a)
    (hargs : WP isa (.block args) s fun u => u.gpr .x1=BitVec.ofNat 64 o ∧
      u.gpr .x2=BitVec.ofNat 64 a ∧ Keeps [.x1,.x2] s u ∧ u.v=s.v) :
    WP isa (.seq (.block args) callNormalDouble) s fun t =>
      canonicalPoint t.mem (s.gpr .x0) o ∧
      ordinaryPoint t.mem (s.gpr .x0) o=dblJF (ordinaryPoint s.mem (s.gpr .x0) a).1
        (ordinaryPoint s.mem (s.gpr .x0) a).2.1 (ordinaryPoint s.mem (s.gpr .x0) a).2.2 ∧
      DoubleFrame (s.gpr .x0) o s.mem t.mem ∧ WindowStable s t := by
  rw [WP.seq_iff]
  refine WP.mono hargs fun u ⟨argO,argA,ku,vu⟩ => ?_
  have u0 := ku.gpr .x0 (by decide)
  have hu : Scr u (u.gpr .x0) W := by rw [u0]; exact hs.of_keeps ku (by decide)
  have bound : canonicalPoint u.mem (u.gpr .x0) a := by rw [u0,ku.mem]; exact ha
  refine WP.mono (window_double_call_ok ⟨hu,room,layout,argO,argA⟩ bound)
    fun t ⟨b,p,frame,zero,rd,wr,sp,gp,v29,v31⟩ => ?_
  rw [u0] at b p frame zero
  rw [ku.mem] at p frame
  have fresh : ∀r∈preserved,r∉[Reg.x1,Reg.x2] := by decide
  exact ⟨b,p,frame,zero,rd.trans ku.rd,wr.trans ku.wr,sp.trans ku.sp,
    fun r hr hn => (gp r hr hn).trans (ku.gpr r (fresh r hr)),by rw [v29,vu],by rw [v31,vu]⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

/-! Two ordinary doubles alternate the buffers and return to the accumulator. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (callNormalDouble outerBlock138 outerBlock139)
open VG.Proof.Weierstrass (dblJF)

def windowDbl (P : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) := dblJF P.1 P.2.1 P.2.2

def WindowWorkFrame (base : Addr) (m m' : Mem) : Prop :=
  ∀x,(ofs base x<1072 ∨ 1504≤ofs base x) →
    (ofs base x<4080 ∨ 4584≤ofs base x) → m' x=m x

 theorem WindowWorkFrame.trans {base : Addr} {m m' m'' : Mem}
    (h : WindowWorkFrame base m m') (k : WindowWorkFrame base m' m'') : WindowWorkFrame base m m'' :=
  fun x a b => (k x a b).trans (h x a b)

 theorem DoubleFrame.window {base : Addr} {o : Nat} {m m' : Mem} (h : DoubleFrame base o m m')
    (lo : 1072≤o) (hi : o+216≤1504) : WindowWorkFrame base m m' := by
  intro x a b
  exact h x (by omega_arith) b

def windowDoublePair : Prog isa :=
  .seq (.seq (.block outerBlock138) callNormalDouble) (.seq (.block outerBlock139) callNormalDouble)

 theorem window_double_pair_ok {s : State} {W : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (bound : canonicalPoint s.mem (s.gpr .x0) 1072) :
    WP isa windowDoublePair s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1072 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1072=windowDbl (windowDbl (ordinaryPoint s.mem (s.gpr .x0) 1072)) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowStable s t := by
  rw [windowDoublePair,WP.seq_iff]
  refine WP.mono (window_double_step_ok hs room double_layout_forward bound (window_args_forward s))
    fun u ⟨bu,pu,fu,ku⟩ => ?_
  have hu := ku.scr hs
  have hb : canonicalPoint u.mem (u.gpr .x0) 1288 := by rw [ku.base]; exact bu
  refine WP.mono (window_double_step_ok hu room double_layout_backward hb (window_args_backward u))
    fun t ⟨bt,pt,ft,kt⟩ => ?_
  rw [ku.base] at bt pt ft
  refine ⟨bt,?_,WindowWorkFrame.trans (DoubleFrame.window fu (by decide) (by decide)) (DoubleFrame.window ft (by decide) (by decide)),ku.trans kt⟩
  change ordinaryPoint t.mem (s.gpr .x0) 1072=windowDbl (ordinaryPoint u.mem (s.gpr .x0) 1288) at pt
  rw [pt,pu]
  rfl

end VG.Proof.Weierstrass.AArch64.P521Native
