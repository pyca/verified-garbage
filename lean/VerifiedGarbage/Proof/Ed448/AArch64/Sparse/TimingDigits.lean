module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.TimingTrim
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.JointDigits
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
meta import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
meta import VerifiedGarbage.Impl.Ed448.WnafWide

/-! Complete relational timing for the sparse multiplier once recoding is complete. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse
open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.WnafWide (digitAt)
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr off)
open VG.Proof.X448.AArch64.Fast (BEnv)
open VG.Proof.Curve448.AArch64.Fast (Mb)

structure DigitsCtx (base tbl:Addr) (S K:Nat) (s:State) : Prop where
  scr : Scr s base
  bnd : BEnv s.mem base
  sd : ∀ i<464,s.mem (off base (SDIG+i))=BitVec.ofInt 8 (digitAt true S i)
  kd : ∀ i<464,s.mem (off base (BITS+i))=BitVec.ofInt 8 (digitAt false K i)
  tab : ∃ P:Spec.Ed448.Point,OddTabOk s.mem base P 8
  xb : ∀ e<8,∀ w<8,(Window.tw s.mem base e w).toNat<Mb
  bt : BaseTableAt s base tbl

private theorem init_ctx {base tbl:Addr} {S K:Nat} {s:State} (h:DigitsCtx base tbl S K s) :
    WP isa (.block init) s (TimingCtx base tbl S K 464):=by
  refine WP.mono (jointInit_ok h.scr h.bnd) fun t ⟨tc,t19,_,tf,tk⟩ => ?_
  have k:JointFrame base s.mem t.mem:=fun x a b _ => tf x a b
  refine ⟨tc,t19,?_,?_,?_,k.xbounds h.xb,h.bt.of_frame (by rw [tk.2.1,tk.2.2]) k⟩
  · intro j hj;rw [k.baseDigit hj];exact h.sd j hj
  · intro j hj;rw [k.keyDigit hj];exact h.kd j hj
  · obtain ⟨P,hp⟩:=h.tab;exact ⟨P,k.oddTable hp⟩

private theorem pin_ctx {sp tbl:Addr} {A B:State → Prop} {p:Prog isa}
    (hw:∀ s,A s → WP isa p s B) {s:State} (h:Pinned sp tbl A s) :
    WP isa p s (Pinned sp tbl B):=wp_pinned hw h

theorem jointDigits_ct (hA:AffineOk) (base tbl sp:Addr) (S K:Nat) :
    RelCT isa (fun s t => Pinned sp tbl (DigitsCtx base tbl S K) s ∧
      Pinned sp tbl (DigitsCtx base tbl S K) t) jointDigits (fun _ _ => True):=by
  unfold jointDigits
  have ha:∀ s t,Pinned sp tbl (DigitsCtx base tbl S K) s ∧
      Pinned sp tbl (DigitsCtx base tbl S K) t →
      Taint.AgreeS [baseSym] (Taint.ofRegs [.x3]) s t:=by
    intro s t h
    refine ⟨⟨h.1.2.1.trans h.2.2.1.symm,?_⟩,?_⟩
    · intro r hr
      obtain rfl:=List.mem_singleton.mp (Taint.mem_ofRegs.mp hr)
      exact h.1.1.scr.x3.trans h.2.1.scr.x3.symm
    · intro n hn;obtain rfl:=List.mem_singleton.mp hn
      exact h.1.2.2.trans h.2.2.2.symm
  apply seq_same (RelCT.taint (A:=taintS [baseSym]) (Taint.ofRegs [.x3]) ha (by taint_decide))
    (fun _ h => pin_ctx (fun _ h => init_ctx h) h)
  apply (trim_ct base tbl sp S K 464 (by decide) (by decide)).seq
  apply RelCT.exists_
  intro i
  by_cases hi:i<464
  · have hw:∀ s,Pinned sp tbl (TimingCtx base tbl S K i) s →
        WP isa (.block [.addImm .x .x19 .x19 1]) s (Pinned sp tbl (TimingCtx base tbl S K (i+1))):=by
      intro s h
      apply pin_ctx (fun s hc => ?_) h
      refine WP.mono (incCounter_ok hc.counter) fun t ⟨t19,tk,tm⟩ => hc.regsOnly tk tm (by decide) t19
    apply (seq_same (RelCT.taint (A:=taintS [baseSym]) (Taint.ofRegs [.x3,.x19])
      (fun _ _ h => timingCtx_agree h) (by taint_decide)) hw
      (jointLoop_ct hA base tbl sp S K (i+1) (by omega) (by omega))).mono
      (fun _ _ h => h.2) (fun _ _ h => h)
  · exact RelCT.of_false (fun _ _ h => hi h.1)

end VG.Proof.Ed448.AArch64.Sparse
