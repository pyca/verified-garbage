module

public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCTLoop
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedWork
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedLoop
import VerifiedGarbage.Proof.Bignum.AArch64.WindowArithmeticCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCTLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedWork
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowArithmeticCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

def FastPre (p : XPub) (s : State) : Prop :=
  ∃ mi X Xc v, TableCtx s (off p.B p.o) p.wx mi X Xc ∧
    CrtWindowFive.CTab s.mem (off p.B p.o) p.wx X False 0 ∧
    16 ≤ p.wx ∧ p.wx < 2^30 ∧ p.wx % 8 = 0 ∧ v < 32 ∧
    word s.mem (off p.B p.o) (8*Crt.sNib) = BitVec.ofNat 64 v

def CorePre (p : XPub) (s : State) : Prop :=
  FastPre p s ∧ word s.mem (off p.B p.o) (8*Crt.sBit) = BitVec.ofNat 64 5

theorem fast_loose {p : XPub} {s : State} (h : FastPre p s) : LooseCtx p s := by
  obtain ⟨mi,X,Xc,v,hc,ht,hw,hw',hd,hv,hn⟩ := h
  exact ⟨mi,X,Xc,hc,hw,hw',hd⟩

theorem squares_post (p : XPub) (s : State) (h : CorePre p s) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.squares s (FastPre p) := by
  obtain ⟨⟨mi,X,Xc,v,hc,ht,hw,hw',hd,hv,hn⟩,hb⟩ := h
  refine WP.mono (squares_ok hc hw hw' hd hb) fun t ⟨ct,_,hh,hf,_⟩ => ?_
  exact ⟨mi,X,Xc,v,ct,ht.of_win hf hc.scrT.nowrap,hw,hw',hd,hv,
    (hh _ (by decide) (by decide)).trans hn⟩

theorem core_ct : RelCT isa (Two CorePre)
    VG.Impl.Rsa.AArch64.WindowShared.core (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowShared.core
  refine RelCT.seq (two_post (two_map id (fun _ _ h => ⟨fast_loose h.1,h.2⟩)
    (loop_ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro))) squares_post) ?_
  refine RelCT.seq (two_post (Ψ := fun p => BlockedRedc.FastW (workspace p))
    (two_map id ?_ WindowVector.blocked_ct) ?_)
    (two_map workspace (fun _ _ h => h) WindowArithmetic.product_ct)
  · rintro p s ⟨mi,X,Xc,v,hc,ht,hw,hw',hd,hv,hn⟩
    exact ⟨⟨mi,X,Xc,v,hc,by change 2 ≤ p.wx; omega,hw',hv,ht.tab,hn⟩,by change 8 ≤ p.wx; omega⟩
  · rintro p s ⟨mi,X,Xc,v,hc,ht,hw,hw',hd,hv,hn⟩
    exact WP.mono (WindowVector.blocked_ok hc (by omega) hw' hd hv ht.tab hn)
      fun t ⟨ct,_⟩ => ⟨⟨mi,ct.good,Nat.le_refl _⟩,hw,hd⟩

theorem init_post (p : XPub) (s : State) (h : FastPre p s) :
    WP isa (.block [movi .x3 5,sth .x3 Crt.sBit]) s (CorePre p) := by
  obtain ⟨mi,X,Xc,v,hc,ht,hw,hw',hd,hv,hn⟩ := h
  refine WP.mono (init_ok hc) fun t ⟨hm,kt⟩ => ?_
  have hout := writeW_outside s.mem (off p.B p.o) (d := 8*Crt.sBit) (BitVec.ofNat 64 5) (by decide)
  rw [← hm] at hout
  have hf : Frm (off p.B p.o) (crtWinRanges p.wx) s.mem t.mem :=
    Frm.of_outside hout (by simp [crtWinRanges])
  refine ⟨⟨mi,X,Xc,v,hc.of_win hf kt.wr (kt.gpr .x0 (by decide)),
    ht.of_win hf hc.scrT.nowrap,hw,hw',hd,hv,?_⟩,?_⟩
  · rw [hm,hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hn
  · rw [hm,word_writeW_self]

theorem work_ct : RelCT isa (Two FastPre)
    VG.Impl.Rsa.AArch64.WindowShared.work (fun _ _ => True) :=
  RelCT.seq (two_piece [.x0] (fun p s t hs ht => pins_loose p s t (fast_loose hs) (fast_loose ht))
    (by taint_decide) init_post) core_ct

end VG.Proof.Bignum.AArch64.WindowShared
