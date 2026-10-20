module

import VerifiedGarbage.Proof.Bignum.AArch64.WindowArithmeticCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowShared
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtContext
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedStep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowArithmeticCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowShared
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedStep
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

def LooseCtx (p : XPub) (s : State) : Prop :=
  ∃ mi X Xc, TableCtx s (off p.B p.o) p.wx mi X Xc ∧ 16 ≤ p.wx ∧ p.wx < 2^30 ∧ p.wx % 8 = 0

def workspace (p : XPub) : Ws := ⟨off p.B p.o,slot p.wx 8,p.wx⟩

theorem loose_fast {p : XPub} {s : State} (h : LooseCtx p s) : BlockedRedc.FastW (workspace p) s := by
  obtain ⟨mi,X,Xc,hc,hw,hw',hd⟩ := h
  exact ⟨⟨mi,hc.good,Nat.le_refl _⟩,hw,hd⟩

theorem pins_loose : Pins LooseCtx [.x0] := by
  intro p s t hs ht r hr
  obtain ⟨_,_,_,cs,_⟩ := hs
  obtain ⟨_,_,_,ct,_⟩ := ht
  have : r = .x0 := by simpa using hr
  subst r
  exact cs.good.x0.trans ct.good.x0.symm

def LoopP (p : XPub) (j : Nat) (s : State) : Prop :=
  LooseCtx p s ∧ word s.mem (off p.B p.o) (8*Crt.sBit) = BitVec.ofNat 64 (5-j)

theorem square_loop_ctx (p : XPub × Nat) (s : State) (h : LoopP p.1 p.2 s) :
    WP isa (VG.Impl.Bignum.AArch64.WindowArithmetic.square 6) s (LoopP p.1 p.2) := by
  obtain ⟨⟨mi,X,Xc,hc,hw,hw',hd⟩,hb⟩ := h
  refine WP.mono (square_ok hc hw hw' hd) fun t ⟨ct,_,hh,_,_⟩ => ?_
  exact ⟨⟨mi,X,Xc,ct,hw,hw',hd⟩,(hh _ (by decide)).trans hb⟩

theorem step_ct : RelCT isa (Two fun p : XPub × Nat => fun s => p.2 < 5 ∧ LoopP p.1 p.2 s)
    VG.Impl.Rsa.AArch64.WindowShared.step (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowShared.step
  refine RelCT.seq (two_post (two_map (fun p : XPub × Nat => workspace p.1)
    (fun _ _ h => loose_fast h.2.1) WindowArithmetic.square_ct)
    (fun p s h => square_loop_ctx p s h.2)) ?_
  exact two_taint [.x0] (fun p s t hs ht => pins_loose p.1 s t hs.1 ht.1) (by taint_decide)

theorem step_loop_ctx (p : XPub) (j : Nat) (s : State) (hj : j < 5) (h : LoopP p j s) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.step s fun t =>
      LoopP p (j+1) t ∧ t.gpr .x3 = BitVec.ofNat 64 (5-(j+1)) := by
  obtain ⟨⟨mi,X,Xc,hc,hw,hw',hd⟩,hb⟩ := h
  refine WP.mono (step_ok (k := 0) (A := wv s.mem (off p.B p.o) (slot p.wx Public.aY) p.wx)
    hc hw hw' hd hj hb (by simp)) fun t ⟨ct,_,hb',h3,_⟩ => ?_
  exact ⟨⟨⟨mi,X,Xc,ct,hw,hw',hd⟩,hb'⟩,h3⟩

theorem loop_ct : RelCT isa (Two fun p s => LoopP p 0 s)
    VG.Impl.Rsa.AArch64.WindowShared.squares (Two fun p s => LoopP p 5 s) := by
  apply RelCT.mono (two_loop (fun _ : XPub => 5) step_ct ?_) (fun _ _ h => ?_) (fun _ _ h => h)
  · intro p j s hj h
    refine WP.mono (step_loop_ctx p j s hj h) fun t ⟨ht,h3⟩ => ?_
    refine ⟨?_,fun _ => ht,fun he => he ▸ ht⟩
    rw [VG.Proof.MlKem.AArch64.eval_nonzero,h3,VG.Proof.MlKem.AArch64.ne_zero_iff,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 5-(j+1) < 2^64 by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · obtain ⟨p,hs,ht,hsp⟩ := h
    exact ⟨p,⟨by decide,hs⟩,⟨by decide,ht⟩,hsp⟩

end VG.Proof.Bignum.AArch64.WindowShared
