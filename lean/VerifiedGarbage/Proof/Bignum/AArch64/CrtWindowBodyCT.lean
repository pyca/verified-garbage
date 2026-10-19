module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunContext
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTakeBitCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoadGroup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoadTail
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailByteCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroupCT
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTakeBitCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoadGroup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoadTail
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailByteCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroupCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.CrtMath

/-! Batch and trailing-byte bodies have public source addresses and control. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (loadGroup appliedBatch appliedGroup groupBody tailBody)

theorem loadGroup_ready {p : RunPub} {i : Nat} {s : State} (hi : i+5 ≤ p.len)
    (h : RunInv p i 0 s) : WP isa (.block loadGroup) s (GroupPre p.ws) := by
  obtain ⟨s0,mi,X,Xc,bs,hI,hw,hw',hR,hL,_,hr,hb,ho⟩ := h
  have hi' : i+5 ≤ bs.length := by omega
  have hb5 : 5 ≤ (bs.drop i).length := by simp only [List.length_drop]; omega
  have hr5 : ∀ j < 5, InRegions (s.rd ++ s.wr) ((p.ep + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) 1 := by
    intro j hj
    rw [hI.keep.rd,hI.keep.wr,BitVec.add_assoc,ofNat_add_ofNat]
    exact hr (i+j) (by omega)
  have hb' : ∀ j (hj : j < 5), s.mem ((p.ep + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) =
      (bs.drop i)[j]'(by simp only [List.length_drop]; omega) := by
    intro j hj
    rw [BitVec.add_assoc,ofNat_add_ofNat,List.getElem_drop]
    exact hI.source hb ho (by omega)
  refine WP.mono (loadGroup_ok hI.ctx hb5 hI.exp hI.idx hr5 hb') fun t ⟨hm,kt⟩ => ?_
  have out := writeW_outside s.mem (off p.ws.B p.ws.o) (d := 8 * Crt.sV)
    (BitVec.ofNat 64 (pre (bs.drop i) 5)) (by decide)
  rw [← hm] at out
  have ft : Frm (off p.ws.B p.ws.o) (crtWinRanges p.ws.wx) s.mem t.mem :=
    Frm.of_outside out (by simp [crtWinRanges])
  obtain ⟨E,v,_,_,_,hy,_⟩ := hI.pending
  have ey : wv t.mem (off p.ws.B p.ws.o) (slot p.ws.wx aY) p.ws.wx =
      wv s.mem (off p.ws.B p.ws.o) (slot p.ws.wx aY) p.ws.wx :=
    out.wv (by have := hdr_lt_slot p.ws.wx aY (show Crt.sV < 32 by decide); omega) (by
      have := hI.ctx.good.scr.nowrap
      have := slot_le (w := p.ws.wx) (show aY < 8 by decide)
      omega)
  exact ⟨mi,X,Xc,pre (bs.drop i) 5,hI.ctx.of_win ft kt.wr (kt.gpr .x0 (by decide)),
    hI.tab.of_win ft hI.ctx.scrT.nowrap,ey.symm ▸ hy,hw,hw',hR,
    by have := pre_lt (bs.drop i) hb5; omega,by rw [hm,word_writeW_self]⟩

theorem appliedGroup_ready (W : Window) (n : Nat) (hn : n ≤ 8) {p : XPub} {s : State}
    (h : GroupPre p s) : WP isa (appliedGroup W.code n) s (GroupPre p) := by
  induction n generalizing s with
  | zero => exact WP.block_nil h
  | succ n ih =>
    exact WP.seq (WP.mono (appliedStep_post W (5*n) (by omega) h) fun _ h => ih (by omega) h)

theorem groupBody_ct (W : Window) :
    RelCT isa (Two fun (p : RunPub × Nat) s => p.2+5 ≤ p.1.len ∧ RunInv p.1 p.2 0 s)
      (groupBody W.code) (fun _ _ => True) := by
  unfold groupBody appliedBatch
  refine RelCT.seq (RelCT.seq (two_post (Ψ := fun p : RunPub × Nat => GroupPre p.1.ws)
    (two_map (fun p : RunPub × Nat => (p.1.ws,p.1.ep,p.2))
      (fun _ _ h => h.2.read) loadGroup_ct) (fun _ _ h => loadGroup_ready h.1 h.2))
    (two_map (fun p : RunPub × Nat => p.1.ws) (fun _ _ h => h)
      (two_post (appliedGroup_ct W 8 (by decide)) (fun _ _ h => appliedGroup_ready W 8 (by decide) h)))) ?_
  exact x0_ct (fun p : XPub => off p.B p.o)
    (fun _ _ ⟨_,_,_,_,hc,_⟩ => hc.good.x0) (by taint_decide)

theorem loadTail_ready {p : RunPub} {i b : Nat} {s : State} (hi : i < p.len)
    (h : RunInv p i b s) :
    WP isa (.block VG.Impl.Rsa.AArch64.WindowFive.loadTailByte) s (TailPre (p.ws,b)) := by
  obtain ⟨s0,mi,X,Xc,bs,hI,hw,hw',hR,hL,_,hr,hb,ho⟩ := h
  have hi' : i < bs.length := by omega
  refine WP.mono (loadTailByte_ok hI.ctx hI.tab hI.pending hI.idx hI.exp
    (by rw [hI.keep.rd,hI.keep.wr]; exact hr i hi') (hI.source hb ho hi'))
    fun t ⟨ct,tt,pt,vt,_⟩ => ?_
  obtain ⟨E,v,hb,hv,_,hy,_,hn,bc⟩ := pt
  exact ⟨mi,X,Xc,v,bs[i].toNat,ct,tt,hy,hw,hw',hb,hv,bs[i].isLt,hn,bc,vt,hR⟩

theorem tailBody_ct (W : Window) :
    RelCT isa (Two fun (p : RunPub × Nat × Nat) s => p.2.1 < p.1.len ∧ RunInv p.1 p.2.1 p.2.2 s)
      (tailBody W.code) (fun _ _ => True) := by
  unfold tailBody
  refine RelCT.seq (two_post (Ψ := fun p : RunPub × Nat × Nat => TailPre (p.1.ws,p.2.2))
    (two_map (fun p : RunPub × Nat × Nat => (p.1.ws,p.1.ep,p.2.1))
      (fun _ _ h => h.2.read) loadTailByte_ct) (fun _ _ h => loadTail_ready h.1 h.2)) ?_
  refine RelCT.seq (two_map (fun p : RunPub × Nat × Nat => (p.1.ws,p.2.2)) (fun _ _ h => h)
    (two_post (tailBits_ct W 8 (by decide)) (fun _ _ h => tailBits_ready W 8 (by decide) h))) ?_
  exact x0_ct (fun p : XPub × Nat => off p.1.B p.1.o)
    (fun _ _ ⟨_,_,_,_,_,hc,_⟩ => hc.good.x0) (by taint_decide)

end VG.Proof.Bignum.AArch64.WindowFive
