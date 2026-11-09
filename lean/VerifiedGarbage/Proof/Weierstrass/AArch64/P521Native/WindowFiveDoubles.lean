module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowDoublePair
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowCounter
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

structure WindowLoopStable (s t : State) : Prop where
  base : t.gpr .x0=s.gpr .x0
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  gp : ∀r∈preserved,r≠.x30 → r≠.x19 → t.gpr r=s.gpr r
  v29 : t.v .v29=s.v .v29
  v31 : t.v .v31=s.v .v31

 theorem WindowLoopStable.trans {s t u : State} (h : WindowLoopStable s t) (k : WindowLoopStable t u) : WindowLoopStable s u :=
  ⟨k.base.trans h.base,k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp,
    fun r hr hn hc => (k.gp r hr hn hc).trans (h.gp r hr hn hc),k.v29.trans h.v29,k.v31.trans h.v31⟩

 theorem WindowLoopStable.scr {s t : State} {W : Nat} (h : WindowLoopStable s t) (hs : Scr s (s.gpr .x0) W) :
    Scr t (t.gpr .x0) W := by
  refine ⟨rfl,?_,?_,hs.enc⟩
  · rw [h.base,h.wr]; exact hs.wr
  · rw [h.base]; exact hs.nowrap

def windowDoubleBody : Prog isa := .seq windowDoublePair (.block outerBlock140)

 theorem window_double_body_ok {s : State} {W j c : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (hj : j<4294967296) (hc : 1≤c) (hc2 : c≤2) (counter : s.gpr .x19=windowPacked j c) :
    WP isa windowDoubleBody s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1072 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1072=windowDbl (windowDbl (ordinaryPoint s.mem (s.gpr .x0) 1072)) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowLoopStable s t ∧
      t.gpr .x19=windowPacked j (c-1) ∧ t.gpr .x2=BitVec.ofNat 64 (c-1) := by
  rw [windowDoubleBody,WP.seq_iff]
  refine WP.mono (window_double_pair_ok hs room bound) fun u ⟨b,p,frame,ku⟩ => ?_
  refine WP.mono (window_counter_pair u) fun t ⟨e19,e2,kt,vt⟩ => ?_
  have uc : u.gpr .x19=windowPacked j c := (ku.gp .x19 (by decide) (by decide)).trans counter
  rw [uc,window_counter_pair_value j c hc] at e19 e2
  rw [window_counter_high j (c-1) hj (by omega_arith)] at e2
  have fresh : ∀r∈preserved,r≠.x19 → r∉[Reg.x19,Reg.x2] := by decide
  refine ⟨?_,?_,?_,?_,e19,e2⟩
  · rw [kt.mem]; exact b
  · rw [kt.mem]; exact p
  · rw [kt.mem]; exact frame
  · exact ⟨(kt.gpr _ (by decide)).trans ku.base,kt.rd.trans ku.rd,kt.wr.trans ku.wr,kt.sp.trans ku.sp,
      fun r hr hn h19 => (kt.gpr r (fresh r hr h19)).trans (ku.gp r hr hn),
      by rw [vt,ku.v29],by rw [vt,ku.v31]⟩

 theorem window_double_body_source {s : State} {Q : State → Prop} :
    WP isa windowDoubleBody s Q ↔ WP isa (sequence [
      .block outerBlock138,callNormalDouble,.block outerBlock139,callNormalDouble,.block outerBlock140]) s Q := by
  simp only [windowDoubleBody,windowDoublePair,sequence,List.foldr_cons,List.foldr_nil,VG.WP.seq_iff (M:=isa),VG.WP.block_nil_iff (M:=isa)]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native

 theorem window_double_loop_one {s : State} {W j : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (hj : j<4294967296) (counter : s.gpr .x19=windowPacked j 1) :
    WP isa loop24 s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1072 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1072=windowDbl (windowDbl (ordinaryPoint s.mem (s.gpr .x0) 1072)) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowLoopStable s t ∧
      t.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x2=0#64 := by
  have body := (window_double_body_source).mp
    (window_double_body_ok hs room bound hj (by decide : 1≤1) (by decide) counter)
  obtain ⟨trace,t,exec,b,p,frame,k,e19,e2⟩ := body
  have cond : isa.eval (.nonzero .x .x2) t=some false := by
    change some (t.gpr .x2 != 0)=some false
    rw [e2]; rfl
  refine ⟨_,t,Exec.loopExit exec cond,b,p,frame,k,?_,e2⟩
  · simpa only [Nat.sub_self,windowPacked,Nat.zero_mul,Nat.add_zero] using e19

 theorem window_double_loop_two {s : State} {W j : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (hj : j<4294967296) (counter : s.gpr .x19=windowPacked j 2) :
    WP isa loop24 s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1072 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1072=
        windowDbl (windowDbl (windowDbl (windowDbl (ordinaryPoint s.mem (s.gpr .x0) 1072)))) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowLoopStable s t ∧
      t.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x2=0#64 := by
  have body := (window_double_body_source).mp
    (window_double_body_ok hs room bound hj (by decide : 1≤2) (by decide) counter)
  obtain ⟨trace,u,exec,b,p,frame,k,e19,e2⟩ := body
  have cond : isa.eval (.nonzero .x .x2) u=some true := by
    change some (u.gpr .x2 != 0)=some true
    rw [e2]; rfl
  have hu := k.scr hs
  have bu : canonicalPoint u.mem (u.gpr .x0) 1072 := by rw [k.base]; exact b
  obtain ⟨trace',t,exec',bt,pt,ft,kt,t19,t2⟩ := window_double_loop_one hu room bu hj e19
  rw [k.base] at bt pt ft
  refine ⟨_,t,Exec.loopNext exec cond exec',bt,?_,WindowWorkFrame.trans frame ft,k.trans kt,t19,t2⟩
  rw [pt,p]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native

 def windowFiveDoubles : Prog isa := .seq loop24 (.seq (.block outerBlock141) callNormalDouble)

 theorem window_five_doubles_ok {s : State} {W j : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (hj : j<4294967296) (counter : s.gpr .x19=windowPacked j 2) :
    WP isa windowFiveDoubles s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1288 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1288=
        windowDbl (windowDbl (windowDbl (windowDbl (windowDbl (ordinaryPoint s.mem (s.gpr .x0) 1072))))) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowLoopStable s t ∧
      t.gpr .x19=BitVec.ofNat 64 j := by
  rw [windowFiveDoubles,WP.seq_iff]
  refine WP.mono (window_double_loop_two hs room bound hj counter) fun u ⟨bu,pu,fu,ku,counterU,_⟩ => ?_
  have hu := ku.scr hs
  have hb : canonicalPoint u.mem (u.gpr .x0) 1072 := by rw [ku.base]; exact bu
  refine WP.mono (window_double_step_ok hu room double_layout_forward hb (window_args_extra u))
    fun t ⟨bt,pt,ft,kt⟩ => ?_
  rw [ku.base] at bt pt ft
  refine ⟨bt,?_,WindowWorkFrame.trans fu (DoubleFrame.window ft (by decide) (by decide)),?_,?_⟩
  · change ordinaryPoint t.mem (s.gpr .x0) 1288=windowDbl (ordinaryPoint u.mem (s.gpr .x0) 1072) at pt
    rw [pt,pu]
  · exact ⟨kt.base.trans ku.base,kt.rd.trans ku.rd,kt.wr.trans ku.wr,kt.sp.trans ku.sp,
      fun r hr hn h19 => (kt.gp r hr hn).trans (ku.gp r hr hn h19),
      kt.v29.trans ku.v29,kt.v31.trans ku.v31⟩
  · exact (kt.gp .x19 (by decide) (by decide)).trans counterU

end VG.Proof.Weierstrass.AArch64.P521Native
