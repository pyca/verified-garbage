module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.TimingLoop
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono
meta import VerifiedGarbage.Impl.Ed448.WnafWide
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.TrimStep

/-! Leading-zero scanning reveals only the two public scalar streams. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse
open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.WnafWide (digitAt)

private theorem trim_ctx {base tbl sp:Addr} {S K i:Nat} {s:State} (hi:i<464)
    (h:Pinned sp tbl (TimingCtx base tbl S K (i+1)) s) :
    WP isa (.block trimStep) s fun t => Pinned sp tbl (TimingCtx base tbl S K i) t ∧
      (t.gpr .x9==0)=decide (digitAt true S i=0 ∧ digitAt false K i=0 ∧ i≠0):=by
  obtain ⟨tr,t,e,t19,t9,tk,tm⟩:=trimStep_ok h.1.core.scr hi h.1.counter
    (baseDigit_bound S i) (by have :=keyDigit_bound K i;omega) (h.1.sd i hi) (h.1.kd i hi)
  exact ⟨tr,t,e,⟨h.1.regsOnly tk tm (by decide) t19,(Exec.sp e).trans h.2.1,
    by rw [Exec.syms e];exact h.2.2⟩,t9⟩

theorem trim_ct (base tbl sp:Addr) (S K n:Nat) (hn:0<n) (hn':n≤464) :
    RelCT isa (fun s t => Pinned sp tbl (TimingCtx base tbl S K n) s ∧
      Pinned sp tbl (TimingCtx base tbl S K n) t)
      (.loop (.block trimStep) (.zero .x .x9)) (fun s t => ∃ i<464,
        Pinned sp tbl (TimingCtx base tbl S K i) s ∧ Pinned sp tbl (TimingCtx base tbl S K i) t):=by
  let I:=fun m s t => 0<m ∧ m≤464 ∧ Pinned sp tbl (TimingCtx base tbl S K m) s ∧
    Pinned sp tbl (TimingCtx base tbl S K m) t
  have hl:=RelCT.loop (M:=isa) (body:=.block trimStep) (c:=.zero .x .x9) (Q:=fun s t => ∃ i<464,Pinned sp tbl (TimingCtx base tbl S K i) s ∧
    Pinned sp tbl (TimingCtx base tbl S K i) t) I
  apply (hl ?_ n).mono (fun _ _ h => ⟨hn,hn',h⟩) (fun _ _ h => h)
  intro m
  by_cases hm:0<m ∧ m≤464
  · obtain ⟨i,rfl⟩:∃ i,m=i+1:=⟨m-1,by omega⟩
    have hi:i<464:=by omega
    have hs:RelCT isa (I (i+1)) (.block trimStep) (fun _ _ => True):=
      RelCT.taint (A:=taintS [baseSym]) (Taint.ofRegs [.x3,.x19])
        (fun _ _ h => timingCtx_agree h.2.2) (by taint_decide)
    apply (hs.wp (fun _ _ h => ⟨trim_ctx hi h.2.2.1,trim_ctx hi h.2.2.2⟩)).mono
      (fun _ _ h => h)
    intro s t h
    obtain ⟨_,⟨hs,s9⟩,⟨ht,t9⟩⟩:=h
    simp only [eval,State.read,BitVec.setWidth_eq,s9,t9]
    refine ⟨trivial,fun _ => ⟨i,hi,hs,ht⟩,?_⟩
    intro hc
    have hd:digitAt true S i=0 ∧ digitAt false K i=0 ∧ i≠0:=of_decide_eq_true (Option.some.inj hc)
    exact ⟨i,by omega,by omega,by omega,hs,ht⟩
  · exact RelCT.of_false (fun _ _ h => hm ⟨h.1,h.2.1⟩)

end VG.Proof.Ed448.AArch64.Sparse
