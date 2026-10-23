module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.TimingAdd
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.JointLoop
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
meta import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
meta import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
meta import VerifiedGarbage.Impl.Ed448.WnafWide

/-! Relational timing for shared doubling and public signed additions. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse
open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.AArch64 (fnCall asFn)
open VG.Impl.Ed448.WnafWide (digitAt)
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off)
open VG.Proof.Curve448.AArch64.Fast (Mb)

structure TimingCtx (base tbl:Addr) (S K n:Nat) (s:State) : Prop where
  core : Core base s
  counter : s.gpr .x19=BitVec.ofNat 64 n
  sd : ∀ i<464,s.mem (off base (SDIG+i))=BitVec.ofInt 8 (digitAt true S i)
  kd : ∀ i<464,s.mem (off base (BITS+i))=BitVec.ofInt 8 (digitAt false K i)
  tab : ∃ P:Spec.Ed448.Point,OddTabOk s.mem base P 8
  xb : ∀ e<8,∀ w<8,(Window.tw s.mem base e w).toNat<Mb
  bt : BaseTableAt s base tbl

theorem TimingCtx.after {base tbl:Addr} {S K n m:Nat} {s t:State}
    (h:TimingCtx base tbl S K n s) (k:PointKeep base s t) (tc:Core base t)
    (t19:t.gpr .x19=BitVec.ofNat 64 m) : TimingCtx base tbl S K m t:=by
  refine ⟨tc,t19,fun i hi => ?_,fun i hi => ?_,?_,k.xbounds h.xb,k.baseTable h.bt⟩
  · rw [k.baseDigit hi];exact h.sd i hi
  · rw [k.keyDigit hi];exact h.kd i hi
  · obtain ⟨P,hp⟩:=h.tab
    exact ⟨P,k.oddTable hp⟩

theorem timingCtx_agree {base tbl sp:Addr} {S K n:Nat} {s t:State}
    (h:Pinned sp tbl (TimingCtx base tbl S K n) s ∧ Pinned sp tbl (TimingCtx base tbl S K n) t) :
    Taint.AgreeS [baseSym] (Taint.ofRegs [.x3,.x19]) s t:=by
  refine ⟨⟨h.1.2.1.trans h.2.2.1.symm,?_⟩,?_⟩
  · intro r hr
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.core.scr.x3.trans h.2.1.core.scr.x3.symm
    · exact h.1.1.counter.trans h.2.1.counter.symm
  · intro a ha
    obtain rfl:=List.mem_singleton.mp ha
    exact h.1.2.2.trans h.2.2.2.symm

private theorem double_analysis : ∃ h,((taintS [baseSym]).check (Taint.ofRegs [.x3,.x19])
    VG.Impl.Ed448.AArch64.Point56.doubleCall h).isSome=true:=by
  apply exists_isSome_of_eraseT
  simp only [Code.eraseT,VG.Impl.Ed448.AArch64.Point56.doubleCall,fnCall,
    VG.Impl.Ed448.AArch64.Point56.doubleFn,asFn,ops_eraseT]
  refine ⟨?h,?g⟩
  case g => taint_decide

private theorem double_ctx {base tbl:Addr} {S K n:Nat} {s:State}
    (h:TimingCtx base tbl S K n s) :
    WP isa VG.Impl.Ed448.AArch64.Point56.doubleCall s (TimingCtx base tbl S K n):=by
  refine WP.mono (Point56.doubleCall_ok h.core.scr h.core.env h.core.zbound)
    fun t ⟨tk,tb,sm,_,_,tz,_,_⟩ => ?_
  have kp:=PointKeep.of_call tk
  exact h.after kp (h.core.after kp tb sm (by decide) (by decide) tz)
    ((kp.regs.1 _ (by decide)).trans h.counter)

private theorem addBase_ctx (hA:AffineOk) {base tbl sp:Addr} {S K i:Nat} {s:State} (hi:i<464)
    (h:Pinned sp tbl (TimingCtx base tbl S K i) s) :
    WP isa addBase s (TimingCtx base tbl S K i):=by
  have bt:BaseTableAt s base (s.syms baseSym):=by rw [h.2.2];exact h.1.bt
  refine WP.mono (addBase_ok hA h.1.core bt hi h.1.counter (baseDigit_bound S i) (h.1.sd i hi))
    fun t ⟨tc,tk,_⟩ => h.1.after tk tc ((tk.regs.1 _ (by decide)).trans h.1.counter)

private theorem addKey_ctx {base tbl:Addr} {S K i:Nat} {s:State} (hi:i<464)
    (h:TimingCtx base tbl S K i s) : WP isa addKey s (TimingCtx base tbl S K i):=by
  obtain ⟨P,hp⟩:=h.tab
  refine WP.mono (addKey_ok h.core hp h.xb hi h.counter (keyDigit_bound K i) (h.kd i hi))
    fun t ⟨tc,tk,_⟩ => h.after tk tc ((tk.regs.1 _ (by decide)).trans h.counter)

theorem TimingCtx.regsOnly {base tbl:Addr} {S K n m:Nat} {s t:State} {rs:List Reg}
    (h:TimingCtx base tbl S K n s) (hk:Keeps rs s t) (hm:t.mem=s.mem)
    (hr:.x3∉rs ∧ .x12∉rs) (hc:t.gpr .x19=BitVec.ofNat 64 m) : TimingCtx base tbl S K m t:=by
  refine ⟨h.core.regsOnly hk hm hr,hc,?_,?_,?_,?_,?_⟩
  · rw [hm];exact h.sd
  · rw [hm];exact h.kd
  · rw [hm];exact h.tab
  · rw [hm];exact h.xb
  · exact ⟨by rw [hk.2.1,hk.2.2];exact h.bt.read,h.bt.far,by rw [hm];exact h.bt.val⟩

private theorem dec_ctx {base tbl:Addr} {S K i:Nat} {s:State} (hi:i<464)
    (h:TimingCtx base tbl S K (i+1) s) :
    WP isa (.block [.subImm .x .x19 .x19 1]) s (TimingCtx base tbl S K i):=by
  refine WP.mono (VG.Proof.X448.AArch64.Weak.decCounter_ok (by omega) h.counter)
    fun t ⟨t19,tg,tm,tr,tw,_⟩ => ?_
  have hk:Keeps [.x19] s t:=⟨fun r hr => tg r (by simpa only [List.mem_singleton] using hr),tr,tw⟩
  exact TimingCtx.regsOnly h hk tm (by decide) t19

private theorem pin_dep {sp tbl:Addr} {A B:State → Prop} {p:Prog isa}
    (hw:∀ s,Pinned sp tbl A s → WP isa p s B) {s:State} (h:Pinned sp tbl A s) :
    WP isa p s (Pinned sp tbl B):=by
  obtain ⟨t,u,e,hb⟩:=hw s h
  exact ⟨t,u,e,hb,(Exec.sp e).trans h.2.1,by rw [Exec.syms e];exact h.2.2⟩

theorem jointStep_ct (hA:AffineOk) (base tbl sp:Addr) (S K i:Nat) (hi:i<464) :
    RelCT isa (fun s t => Pinned sp tbl (TimingCtx base tbl S K (i+1)) s ∧
      Pinned sp tbl (TimingCtx base tbl S K (i+1)) t) step (fun _ _ => True):=by
  unfold step
  apply seq_same (RelCT.taint (A:=taintS [baseSym]) (Taint.ofRegs [.x3,.x19])
    (fun _ _ h => timingCtx_agree h) (by taint_decide)) (fun _ h => wp_pinned (fun _ h => dec_ctx hi h) h)
  obtain ⟨dh,da⟩:=double_analysis
  apply seq_same (RelCT.taint (A:=taintS [baseSym]) (Taint.ofRegs [.x3,.x19])
    (fun _ _ h => timingCtx_agree h) da) (fun _ h => wp_pinned (fun _ h => double_ctx h) h)
  have ba:=addBase_ct base sp tbl i hi (digitAt true S i) (baseDigit_bound S i)
  have ka:=addKey_ct base sp tbl i hi (digitAt false K i) (by have :=keyDigit_bound K i;omega)
  apply seq_same (ba.mono (fun _ _ h => ⟨⟨⟨h.1.1.core.scr,h.1.1.counter,h.1.1.sd i hi⟩,h.1.2⟩,
    ⟨⟨h.2.1.core.scr,h.2.1.counter,h.2.1.sd i hi⟩,h.2.2⟩⟩) (fun _ _ h => h))
    (fun _ h => pin_dep (fun _ h => addBase_ctx hA hi h) h)
  apply seq_same (ka.mono (fun _ _ h => ⟨⟨⟨h.1.1.core.scr,h.1.1.counter,h.1.1.kd i hi⟩,h.1.2⟩,
    ⟨⟨h.2.1.core.scr,h.2.1.counter,h.2.1.kd i hi⟩,h.2.2⟩⟩) (fun _ _ h => h))
    (fun _ h => wp_pinned (fun _ h => addKey_ctx hi h) h)
  exact RelCT.taint (A:=taintS [baseSym]) (Taint.ofRegs [.x3,.x19])
    (fun _ _ h => timingCtx_agree h) (by taint_decide)

private theorem step_ctx (hA:AffineOk) {base tbl sp:Addr} {S K i:Nat} {s:State} (hi:i<464)
    (h:Pinned sp tbl (TimingCtx base tbl S K (i+1)) s) :
    WP isa step s fun t => Pinned sp tbl (TimingCtx base tbl S K i) t ∧
      t.gpr .x9=BitVec.ofNat 64 i:=by
  obtain ⟨P,hp⟩:=h.1.tab
  have bt:BaseTableAt s base (s.syms baseSym):=by rw [h.2.2];exact h.1.bt
  obtain ⟨tr,t,e,tc,tk,t19,t9,_⟩:=jointStep_ok hA h.1.core hp h.1.xb bt hi h.1.counter
    (baseDigit_bound S i) (keyDigit_bound K i) (h.1.sd i hi) (h.1.kd i hi)
  refine ⟨tr,t,e,⟨⟨tc,t19,?_,?_,⟨P,tk.mem.oddTable hp⟩,tk.mem.xbounds h.1.xb,?_⟩,
    (Exec.sp e).trans h.2.1,by rw [Exec.syms e];exact h.2.2⟩,t9⟩
  · intro j hj;rw [tk.mem.baseDigit hj];exact h.1.sd j hj
  · intro j hj;rw [tk.mem.keyDigit hj];exact h.1.kd j hj
  · exact h.1.bt.of_frame (by rw [tk.regs.2.1,tk.regs.2.2]) tk.mem

private theorem counter_zero : ∀ i<464,(BitVec.ofNat 64 i==0)=decide (i=0):=by decide +kernel

theorem jointLoop_ct (hA:AffineOk) (base tbl sp:Addr) (S K n:Nat) (hn:0<n) (hn':n≤464) :
    RelCT isa (fun s t => Pinned sp tbl (TimingCtx base tbl S K n) s ∧
      Pinned sp tbl (TimingCtx base tbl S K n) t)
      (.loop step (.nonzero .x .x9)) (fun _ _ => True):=by
  let I:=fun m s t => 0<m ∧ m≤464 ∧ Pinned sp tbl (TimingCtx base tbl S K m) s ∧
    Pinned sp tbl (TimingCtx base tbl S K m) t
  have hl:=RelCT.loop (M:=isa) (body:=step) (c:=.nonzero .x .x9) (Q:=fun _ _ => True) I
  apply (hl ?_ n).mono (fun _ _ h => ⟨hn,hn',h⟩) (fun _ _ h => h)
  intro m
  by_cases hm:0<m ∧ m≤464
  · obtain ⟨i,rfl⟩:∃ i,m=i+1:=⟨m-1,by omega⟩
    have hi:i<464:=by omega
    have hs:RelCT isa (I (i+1)) step (fun _ _ => True):=
      (jointStep_ct hA base tbl sp S K i hi).mono (fun _ _ h => h.2.2) (fun _ _ h => h)
    apply (hs.wp (fun _ _ h => ⟨step_ctx hA hi h.2.2.1,step_ctx hA hi h.2.2.2⟩)).mono
      (fun _ _ h => h)
    intro s t h
    obtain ⟨_,⟨hs,s9⟩,⟨ht,t9⟩⟩:=h
    simp only [eval,State.read,BitVec.setWidth_eq,s9,t9,bne,counter_zero i hi]
    refine ⟨trivial,fun _ => trivial,?_⟩
    intro hc
    have hn:i≠0:=by intro hz;subst i;exact Bool.noConfusion (Option.some.inj hc)
    exact ⟨i,by omega,by omega,by omega,hs,ht⟩
  · exact RelCT.of_false (fun _ _ h => hm ⟨h.1,h.2.1⟩)

end VG.Proof.Ed448.AArch64.Sparse
