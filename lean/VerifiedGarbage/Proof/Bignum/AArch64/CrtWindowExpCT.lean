module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHead
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReset
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReset
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.CrtMath
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTableCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTableCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTails
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTails
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingInv
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTakeBit
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingInv
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTakeBit
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPrefixInv
import VerifiedGarbage.Proof.Bignum.CrtWindowFive
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinish
import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPrefixInv
meta import VerifiedGarbage.Proof.Bignum.CrtWindowFive
meta import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

/-! ### `Bignum.AArch64.CrtWindowBodyCT`, which only this module used -/

section

/-! ### `Bignum.AArch64.CrtWindowRunContext`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowCoreCT`, which this module and modules that import it used -/

section

/-! Constant-time composition of a five-bit window. Only workspace layout
is shared between runs; the modulus, table and selected digit are secret. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

def WindowPre (p : XPub) (s : State) : Prop :=
  ∃ mi X Xc v, TableCtx s (off p.B p.o) p.wx mi X Xc ∧
    CrtWindowFive.CTab s.mem (off p.B p.o) p.wx X False 0 ∧
    wv s.mem (off p.B p.o) (slot p.wx aY) p.wx < X ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.wx)) X ∧ v < 32 ∧
    word s.mem (off p.B p.o) (8 * Crt.sNib) = BitVec.ofNat 64 v

theorem WindowPre.sel {p : XPub} {s : State} (h : WindowPre p s) : SelP p s := by
  obtain ⟨mi, X, Xc, v, hc, ht, _, hw, hw', _, hv, hn⟩ := h
  exact ⟨mi, X, Xc, v, hc, hw, hw', hv, ht.tab, hn⟩

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowFinishCT`, which only this module used -/

section

/-! The final partial window branches and loops only on its public bit count. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (finishSquare finish)

def FinishPre (p : XPub × Nat) (s : State) : Prop :=
  WindowPre p.1 s ∧ p.2 < 5 ∧
  word s.mem (off p.1.B p.1.o) (8 * Crt.sBit) = BitVec.ofNat 64 p.2

theorem finishSquare_ct (M : Mont) :
    RelCT isa (Two FinishPre) (finishSquare M.mm) (fun _ _ => True) := by
  unfold finishSquare
  refine RelCT.seq (two_post (Ψ := fun p : XPub × Nat => GoodW p.1.ws)
    (two_map (fun p : XPub × Nat => p.1.ws)
      (fun _ _ ⟨⟨mi,_,_,_,hc,_⟩,_⟩ => ⟨mi,hc.good,Nat.le_refl _⟩)
      (M.ct (by simp [MmUse]))) ?_) ?_
  · rintro p s ⟨⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hR,hv,hn⟩,_⟩
    exact WP.mono (crtSq_ok M (Q := False) (x := 0) (E := 0)
      hc.base hw hw' hR hy False.elim) fun t ⟨ct,_⟩ => ⟨mi,ct.good,Nat.le_refl _⟩
  · apply x0_ct (fun p : XPub × Nat => off p.1.B p.1.o) ?_ (by taint_decide)
    exact fun _ _ ⟨_,hc,_⟩ => hc.x0

theorem finishSquare_post (M : Mont) {p : XPub × Nat} {s : State}
    (h : FinishPre p s) (hb : 0 < p.2) :
    WP isa (finishSquare M.mm) s fun t =>
      FinishPre (p.1,p.2 - 1) t ∧ t.gpr .x3 = BitVec.ofNat 64 (p.2 - 1) := by
  obtain ⟨⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hR,hv,hn⟩,hb',bc⟩ := h
  refine WP.mono (finishSquare_ok M hc ht hw hw' hR hy (Q := False) (x := 0) (E := 0)
    False.elim hb bc) fun t ⟨ct,tt,yt,_,bt,h3,_,_,hh⟩ => ?_
  exact ⟨⟨⟨mi,X,Xc,v,ct,tt,yt,hw,hw',hR,hv,
    (hh _ (by decide) (by decide)).trans hn⟩,by omega,bt⟩,h3⟩

theorem finishSquares_ct (M : Mont) :
    RelCT isa (Two fun p s => 0 < p.2 ∧ FinishPre p s)
      (.loop (finishSquare M.mm) (.nonzero .x .x3))
      (Two fun (p : XPub × Nat) s => FinishPre (p.1,0) s) := by
  refine two_loop (Φ := fun (p : XPub × Nat) i => FinishPre (p.1,p.2-i)) Prod.snd ?_ ?_
  · exact two_map (fun p : (XPub × Nat) × Nat => (p.1.1,p.1.2-p.2))
      (fun _ _ h => h.2) (finishSquare_ct M)
  · intro p i s hi hs
    refine WP.mono (finishSquare_post M hs (by omega)) fun t ⟨ht,h3⟩ => ?_
    refine ⟨?_,?_,?_⟩
    · exact eval_nz_count hi (by rw [h3,cnt_ne (by have := hs.2.1; omega_using [this])]; omega_using [hi])
    · intro _; simpa only [Nat.sub_sub] using ht
    · intro he; simpa only [Nat.sub_sub,he,Nat.sub_self] using ht

theorem selectProduct_ct (M : Mont) (S : Selector) :
    RelCT isa (Two WindowPre) (.seq S.code (M.mm aY aY Crt.aT)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p : XPub => GoodW p.ws)
    (two_map id (fun _ _ h => h.sel) S.ct) ?_)
    (two_map (fun p : XPub => p.ws) (fun _ _ h => h)
      (M.ct (o := aY) (a := aY) (b := Crt.aT) (by unfold MmUse; decide)))
  rintro p s ⟨mi,X,Xc,v,hc,ht,_,hw,hw',_,hv,hn⟩
  exact WP.mono (S.ok hc hw hw' hv ht.tab hn) fun t ⟨ct,_⟩ =>
    ⟨mi,ct.good,Nat.le_refl _⟩

def FinishReady (p : XPub × Nat) (s : State) : Prop :=
  FinishPre p s ∧ s.gpr .x3 = BitVec.ofNat 64 p.2

theorem finishLoad_post {p : XPub × Nat} {s : State} (h : FinishPre p s) :
    WP isa (.block [ldh .x3 Crt.sBit]) s (FinishReady p) := by
  obtain ⟨⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hR,hv,hn⟩,hb,bc⟩ := h
  refine WP.mono (finishLoad_ok hc bc) fun t ⟨⟨hm,h3⟩,kt⟩ => ?_
  have hf : Frm (off p.1.B p.1.o) (crtWinRanges p.1.wx) s.mem t.mem := hm.symm ▸ Frm.refl _ _ _
  exact ⟨⟨⟨mi,X,Xc,v,hc.of_win hf kt.wr (kt.gpr .x0 (by decide)),ht.of_win hf hc.scrT.nowrap,
    hm.symm ▸ hy,hw,hw',hR,hv,hm.symm ▸ hn⟩,hb,hm.symm ▸ bc⟩,h3⟩

theorem finish_ct (M : Mont) (S : Selector) :
    RelCT isa (Two FinishPre) (finish M.mm S.code) (fun _ _ => True) := by
  unfold finish
  refine RelCT.seq (two_post (Ψ := FinishReady)
    (x0_ct (fun p : XPub × Nat => off p.1.B p.1.o)
      (fun _ _ ⟨⟨_,_,_,_,hc,_⟩,_⟩ => hc.good.x0) (by taint_decide))
    (fun _ _ h => finishLoad_post h)) ?_
  refine two_ite ?_ ?_ ?_
  · intro p s t hs ht
    change some (!(s.gpr .x3 == 0)) = some (!(t.gpr .x3 == 0))
    rw [hs.2,ht.2]
  · refine RelCT.seq (two_map id ?_ (finishSquares_ct M))
      (two_map (fun p : XPub × Nat => p.1) (fun _ _ h => h.1) (selectProduct_ct M S))
    intro p s ⟨hs,he⟩
    refine ⟨?_,hs.1⟩
    change 0 < p.2
    by_contra hz
    have hb : p.2 = 0 := by omega_using [hz]
    change some (!(s.gpr .x3 == 0)) = some true at he
    rw [hs.2,hb] at he
    contradiction
  · apply two_taint [] (hc := .block [])
    · intro _ _ _ _ _ r hr; simp at hr
    · rfl

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowReadCT`, which only this module used -/

section

/-! Exponent bytes remain secret; their addresses are public. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (loadGroup groupBytes loadTailByte)

def ReadPre (p : XPub × Addr × Nat) (s : State) : Prop :=
  ∃ mi X Xc, TableCtx s (off p.1.B p.1.o) p.1.wx mi X Xc ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sExp) = p.2.1 ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sI) = BitVec.ofNat 64 p.2.2

def ReadReady (p : XPub × Addr × Nat) (s : State) : Prop :=
  s.gpr .x0 = off p.1.B p.1.o ∧ s.gpr .x3 = p.2.1 + BitVec.ofNat 64 p.2.2

theorem readAddr_ct : RelCT isa (Two ReadPre) (.block byteAddr) (Two ReadReady) := by
  refine two_post (x0_ct (fun p : XPub × Addr × Nat => off p.1.B p.1.o)
    (fun _ _ ⟨_,_,_,hc,_⟩ => hc.good.x0) (by taint_decide)) ?_
  rintro p s ⟨mi,X,Xc,hc,he,hi⟩
  exact WP.mono (byteAddr_run hc.base he hi) fun t ⟨h3,kt⟩ =>
    ⟨(kt.gpr .x0 (by decide)).trans hc.good.x0,h3⟩

theorem pins_readReady : Pins ReadReady [.x0,.x3] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.1.trans ht.1.symm
  · exact hs.2.trans ht.2.symm

theorem loadGroup_ct : RelCT isa (Two ReadPre) (.block loadGroup) (fun _ _ => True) := by
  change RelCT isa (Two ReadPre)
    (.block (byteAddr ++ ([movi .x4 0] ++ groupBytes 5 ++ [sth .x4 Crt.sV]))) _
  exact RelCT.block_append (RelCT.seq readAddr_ct (two_taint [.x0,.x3] pins_readReady (by taint_decide)))

theorem loadTailByte_ct : RelCT isa (Two ReadPre) (.block loadTailByte) (fun _ _ => True) := by
  change RelCT isa (Two ReadPre)
    (.block (byteAddr ++ [.ldrb .x3 .x3 0,sth .x3 Crt.sV])) _
  exact RelCT.block_append (RelCT.seq readAddr_ct (two_taint [.x0,.x3] pins_readReady (by taint_decide)))

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! Only the workspace layout, exponent address, length, and progress are public. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum

structure RunPub where
  ws : XPub
  ep : Addr
  len : Nat

def RunInv (p : RunPub) (i b : Nat) (t : State) : Prop :=
  ∃ (s : State) (mi : BitVec 64) (X Xc : Nat) (bs : List Byte), PrefixInv s (off p.ws.B p.ws.o) p.ws.wx mi X Xc False 0 p.ep bs i b t ∧
    2 ≤ p.ws.wx ∧ p.ws.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.ws.wx)) X ∧
    bs.length = p.len ∧ p.len < 2 ^ 64 ∧
    (∀ j < bs.length, InRegions (s.rd ++ s.wr) (p.ep + BitVec.ofNat 64 j) 1) ∧
    (∀ j (hj : j < bs.length), s.mem (p.ep + BitVec.ofNat 64 j) = bs[j]) ∧
    (∀ j < bs.length, slot p.ws.wx 8 + CrtWindowFive.tabBytes32 p.ws.wx ≤
      ofs (off p.ws.B p.ws.o) (p.ep + BitVec.ofNat 64 j))

theorem RunInv.read {p : RunPub} {i b : Nat} {t : State} (h : RunInv p i b t) :
    ReadPre (p.ws,p.ep,i) t := by
  obtain ⟨s,mi,X,Xc,bs,hI,_⟩ := h
  exact ⟨mi,X,Xc,hI.ctx,hI.exp,hI.idx⟩

theorem RunInv.x0 {p : RunPub} {i b : Nat} {t : State} (h : RunInv p i b t) :
    t.gpr .x0 = off p.ws.B p.ws.o := by
  obtain ⟨s,mi,X,Xc,bs,hI,_⟩ := h
  exact hI.ctx.good.x0

theorem RunInv.finish {p : RunPub} {i b : Nat} {t : State} (h : RunInv p i b t) :
    FinishPre (p.ws,b) t := by
  obtain ⟨s,mi,X,Xc,bs,hI,hw,hw',hR,_⟩ := h
  obtain ⟨E,v,hb,hv,_,hy,_,hn,bc⟩ := hI.pending
  exact ⟨⟨mi,X,Xc,v,hI.ctx,hI.tab,hy,hw,hw',hR,CrtWindowFive.pending_index hv hb,hn⟩,hb,bc⟩

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowAppliedGroupCT`, which only this module used -/

section

/-! ### `Bignum.AArch64.CrtWindowGroupCT`, which this module and modules that import it used -/

section

/-! Constant-time composition of a full group. Its value remains secret. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Rsa.AArch64.WindowFive (groupDigit windowCore groupWindows)

def GroupPre (p : XPub) (s : State) : Prop :=
  ∃ mi X Xc V, TableCtx s (off p.B p.o) p.wx mi X Xc ∧
    CrtWindowFive.CTab s.mem (off p.B p.o) p.wx X False 0 ∧
    wv s.mem (off p.B p.o) (slot p.wx aY) p.wx < X ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.wx)) X ∧ V < 2 ^ 64 ∧
    word s.mem (off p.B p.o) (8 * Crt.sV) = BitVec.ofNat 64 V

theorem digit_ready (shift : Nat) (hs : shift < 64) {p : XPub} {s : State}
    (h : GroupPre p s) :
    WP isa (.block (groupDigit shift)) s (WindowPre p) := by
  obtain ⟨mi, X, Xc, V, hc, ht, hy, hw, hw', hR, hV', hV⟩ := h
  refine WP.mono (groupDigit_ok hc.base hV hV' hs) fun a ⟨hm, ka⟩ => ?_
  have oa := writeW_outside s.mem (off p.B p.o) (d := 8 * Crt.sNib)
    (BitVec.ofNat 64 (V / 2 ^ shift % 32)) (by decide)
  rw [← hm] at oa
  have fa : Frm (off p.B p.o) (crtWinRanges p.wx) s.mem a.mem :=
    Frm.of_outside oa (by simp [crtWinRanges])
  have ya : wv a.mem (off p.B p.o) (slot p.wx aY) p.wx =
      wv s.mem (off p.B p.o) (slot p.wx aY) p.wx :=
    oa.wv (by have := hdr_lt_slot p.wx aY (show Crt.sNib < 32 by decide); omega_using [this])
      (by have := hc.good.scr.nowrap
          have := slot_le (w := p.wx) (show aY < 8 by decide); omega_arith)
  exact ⟨mi, X, Xc, V / 2 ^ shift % 32,
    hc.of_win fa ka.wr (ka.gpr .x0 (by decide)), ht.of_win fa hc.scrT.nowrap,
    ya.symm ▸ hy, hw, hw', hR, Nat.mod_lt _ (by decide), by rw [hm, word_writeW_self]⟩

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! Constant-time composition of a full group. Its value remains secret. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Rsa.AArch64.WindowFive (groupDigit appliedGroup)

theorem appliedStep_ct (W : Window) (shift : Nat) (hs : shift < 64) :
    RelCT isa (Two GroupPre) (.seq (.block (groupDigit shift)) W.code)
      (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := WindowPre)
    (two_map (fun p : XPub => off p.B p.o) ?_ (groupDigit_ct shift))
    (fun _ _ h => digit_ready shift hs h)) (two_map id (fun _ _ ⟨mi,X,Xc,v,hc,ht,hy,hw,hw',_,hv,hn⟩ =>
      ⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hv,hn⟩) W.ct)
  rintro p s ⟨_, _, _, _, hc, _⟩
  exact hc.good.x0

theorem appliedStep_post (W : Window) (shift : Nat) (hs : shift < 64)
    {p : XPub} {s : State} (h : GroupPre p s) :
    WP isa (.seq (.block (groupDigit shift)) W.code) s (GroupPre p) := by
  obtain ⟨mi, X, Xc, V, hc, ht, hy, hw, hw', hR, hV', hV⟩ := h
  exact WP.mono (appliedStep_ok W (Q := False) (x := 0) (E := 0)
    hc ht hw hw' hR hy False.elim hV hV' hs)
    fun t ⟨ct, tt, yt, _, hVt, _⟩ => ⟨mi, X, Xc, V, ct, tt, yt, hw, hw', hR, hV', hVt⟩

theorem appliedGroup_ct (W : Window) (n : Nat) (hn : n ≤ 8) :
    RelCT isa (Two GroupPre) (appliedGroup W.code n) (fun _ _ => True) := by
  induction n with
  | zero =>
    exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (hc := .block []) rfl
  | succ n ih =>
    exact RelCT.seq (two_post (appliedStep_ct W (5 * n) (by omega_using [hn]))
      (fun _ _ h => appliedStep_post W (5 * n) (by omega_using [hn]) h)) (ih (by omega_using [hn]))

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowTailByteCT`, which only this module used -/

section

/-! ### `Bignum.AArch64.CrtWindowTakeBitCT`, which this module and modules that import it used -/

section

/-! A tail bit's branch depends only on the public pending-bit count. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (takeBit)

def TailPre (p : XPub × Nat) (s : State) : Prop :=
  ∃ mi X Xc v V, TableCtx s (off p.1.B p.1.o) p.1.wx mi X Xc ∧
    CrtWindowFive.CTab s.mem (off p.1.B p.1.o) p.1.wx X False 0 ∧
    wv s.mem (off p.1.B p.1.o) (slot p.1.wx aY) p.1.wx < X ∧
    2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧ p.2 < 5 ∧ v < 2 ^ p.2 ∧ V < 256 ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sNib) = BitVec.ofNat 64 v ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sBit) = BitVec.ofNat 64 p.2 ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sV) = BitVec.ofNat 64 V ∧
    Nat.Coprime (2 ^ (64 * p.1.wx)) X

structure TailReady (p : XPub × Nat) (s : State) : Prop where
  raw : RawWindowPre p.1 s
  flag : s.gpr .x3 = BitVec.ofNat 64 (p.2 + 1) - BitVec.ofNat 64 5

theorem prepare_ready {i : Nat} (hi : i < 8) {p : XPub × Nat} {s : State}
    (h : TailPre p s) :
    WP isa (.block (VG.Impl.Rsa.AArch64.WindowFive.prepareBit i)) s (TailReady p) := by
  obtain ⟨mi,X,Xc,v,V,hc,ht,hy,hw,hw',hb,hv,hV,hn,bc,byc,_⟩ := h
  refine WP.mono (prepareBit_state hc hi (pending_lt16 hb hv) hV hn bc byc)
    fun u ⟨cu,yu,nu,_,fu,_,_,flag⟩ => ?_
  exact ⟨⟨mi,X,Xc,2 * v + V / 2 ^ (7 - i) % 2,cu,
    ht.of_win fu hc.scrT.nowrap,yu.symm ▸ hy,hw,hw',by have := pending_lt16 hb hv; omega_using [this],nu⟩,flag⟩

theorem takeBit_ct (W : Window) {i : Nat} (hi : i < 8) :
    RelCT isa (Two TailPre) (takeBit W.code i) (fun _ _ => True) := by
  unfold takeBit
  refine RelCT.seq (two_post (Ψ := TailReady)
    (two_map (fun p : XPub × Nat => off p.1.B p.1.o)
      (fun _ _ ⟨_,_,_,_,_,hc,_⟩ => hc.good.x0) (prepareBit_ct i))
    (fun _ _ h => prepare_ready hi h)) ?_
  refine two_ite (Φ := TailReady) ?_ ?_ ?_
  · intro p s t hs ht
    change some (s.gpr .x3 == 0) = some (t.gpr .x3 == 0)
    rw [hs.flag,ht.flag]
  · exact two_map Prod.fst (fun _ _ h => h.1.raw) W.ct
  · apply two_taint [] (hc := .block [])
    · intro _ _ _ _ _ r hr; simp at hr
    · rfl

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! Constant time through all tail bits, with a public pending-bit counter. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (takeBit tailBits)

theorem takeBit_ready (W : Window) {i : Nat} (hi : i < 8) {p : XPub × Nat} {s : State}
    (h : TailPre p s) :
    WP isa (takeBit W.code i) s (TailPre (p.1, (p.2 + 1) % 5)) := by
  obtain ⟨mi,X,Xc,v,V,hc,ht,hy,hw,hw',hb,hv,hV,hn,bc,byc,hR⟩ := h
  refine WP.mono (takeBit_pending W hc ht hw hw' hR
    (b := p.2) (K := v) (x := 0) (Q := False)
    ⟨0,v,hb,hv,by simp,hy,fun h => h.elim,hn,bc⟩ hi hV byc)
    fun t ⟨ct,tt,pt,_,_,hh⟩ => ?_
  obtain ⟨E,v',hb',hv',_,hy',_,hn',bc'⟩ := pt
  exact ⟨mi,X,Xc,v',V,ct,tt,hy',hw,hw',hb',hv',hV,hn',bc',
    (hh _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans byc,hR⟩

theorem tailBits_ready (W : Window) (n : Nat) (hn : n ≤ 8) {p : XPub × Nat} {s : State}
    (h : TailPre p s) :
    WP isa (tailBits W.code n) s (TailPre (p.1, (p.2 + n) % 5)) := by
  induction n with
  | zero =>
    apply WP.block_nil
    have hb : p.2 < 5 := by obtain ⟨_,_,_,_,_,_,_,_,_,_,hb,_⟩ := h; exact hb
    simpa only [Nat.add_zero, Nat.mod_eq_of_lt hb] using h
  | succ n ih =>
    unfold tailBits
    refine WP.seq (WP.mono (ih (by omega_using [hn])) fun u hu => ?_)
    refine WP.mono (takeBit_ready W (by omega_using [hn]) hu) fun t ht => ?_
    have he : ((p.2 + n) % 5 + 1) % 5 = (p.2 + (n + 1)) % 5 := by omega_using []
    simpa only [he] using ht

theorem tailBits_ct (W : Window) (n : Nat) (hn : n ≤ 8) :
    RelCT isa (Two TailPre) (tailBits W.code n) (fun _ _ => True) := by
  induction n with
  | zero =>
    apply two_taint [] (hc := .block [])
    · intro _ _ _ _ _ r hr; simp at hr
    · rfl
  | succ n ih =>
    unfold tailBits
    refine RelCT.seq (two_post (Ψ := fun p s => TailPre (p.1, (p.2 + n) % 5) s)
      (ih (by omega_using [hn])) (fun _ _ h => tailBits_ready W n (by omega_using [hn]) h)) ?_
    exact two_map (fun p : XPub × Nat => (p.1, (p.2 + n) % 5))
      (fun _ _ h => h) (takeBit_ct W (by omega_using [hn]))

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowRunPost`, which the modules that import this one used -/

section

/-! Functional postconditions used to carry the constant-time loop invariants. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (groupBody tailBody haveFive remaining expGroups expTail)

theorem RunInv.groupStep (W : Window) {p : RunPub} {i : Nat} {t : State}
    (h : RunInv p i 0 t) (hi : i+5 ≤ p.len) :
    WP isa (groupBody W.code) t fun u => RunInv p (i+5) 0 u ∧
      u.gpr .x9 = if i+10 ≤ p.len then 1 else 0 := by
  obtain ⟨s,mi,X,Xc,bs,hI,hw,hw',hR,hL,hL',hr,hb,ho⟩ := h
  refine WP.mono (groupBody_ok W hw hw' hR (by omega_using [hL, hL']) (by omega_using [hi, hL]) hr hb ho hI)
    fun u ⟨hu,h9⟩ => ?_
  exact ⟨⟨s,mi,X,Xc,bs,hu,hw,hw',hR,hL,hL',hr,hb,ho⟩,by simpa only [hL] using h9⟩

theorem RunInv.tailStep (W : Window) {p : RunPub} {i b : Nat} {t : State}
    (h : RunInv p i b t) (hi : i < p.len) :
    WP isa (tailBody W.code) t fun u => RunInv p (i+1) ((b+8)%5) u ∧
      u.gpr .x3 = BitVec.ofNat 64 (p.len-(i+1)) := by
  obtain ⟨s,mi,X,Xc,bs,hI,hw,hw',hR,hL,hL',hr,hb,ho⟩ := h
  refine WP.mono (tailBody_ok W hw hw' hR (by omega_using [hi, hL]) hr hb ho hI) fun u ⟨hu,h3⟩ => ?_
  exact ⟨⟨s,mi,X,Xc,bs,hu,hw,hw',hR,hL,hL',hr,hb,ho⟩,by simpa only [hL] using h3⟩

theorem RunInv.haveFive {p : RunPub} {i b : Nat} {t : State}
    (h : RunInv p i b t) (hi : i ≤ p.len) :
    WP isa (.block haveFive) t fun u => RunInv p i b u ∧
      u.gpr .x9 = if i+5 ≤ p.len then 1 else 0 := by
  obtain ⟨s,mi,X,Xc,bs,hI,hw,hw',hR,hL,hL',hr,hb,ho⟩ := h
  refine WP.mono (haveFive_ok hI.ctx hi hL' hI.idx (hL ▸ hI.len)) fun u ⟨⟨hm,h9⟩,ku⟩ => ?_
  exact ⟨⟨s,mi,X,Xc,bs,hI.keepMem hm ku (by decide) (by decide),hw,hw',hR,hL,hL',hr,hb,ho⟩,h9⟩

theorem RunInv.remaining {p : RunPub} {i b : Nat} {t : State}
    (h : RunInv p i b t) (hi : i ≤ p.len) :
    WP isa (.block remaining) t fun u => RunInv p i b u ∧ u.gpr .x3 = BitVec.ofNat 64 (p.len-i) := by
  obtain ⟨s,mi,X,Xc,bs,hI,hw,hw',hR,hL,hL',hr,hb,ho⟩ := h
  refine WP.mono (remaining_ok hI.ctx hi hI.idx (hL ▸ hI.len)) fun u ⟨⟨hm,h3⟩,ku⟩ => ?_
  exact ⟨⟨s,mi,X,Xc,bs,hI.keepMem hm ku (by decide) (by decide),hw,hw',hR,hL,hL',hr,hb,ho⟩,h3⟩

theorem RunInv.groups (W : Window) {p : RunPub} {t : State} (h : RunInv p 0 0 t) :
    WP isa (expGroups W.code) t (RunInv p (5*(p.len/5)) 0) := by
  obtain ⟨s,mi,X,Xc,bs,hI,hw,hw',hR,hL,hL',hr,hb,ho⟩ := h
  refine WP.mono (expGroups_ok W hw hw' hR (by omega_using [hL, hL']) hr hb ho hI) fun u hu => ?_
  exact ⟨s,mi,X,Xc,bs,by simpa only [hL] using hu,hw,hw',hR,hL,hL',hr,hb,ho⟩

theorem RunInv.tails (W : Window) {p : RunPub} {i : Nat} {t : State}
    (h : RunInv p i 0 t) (hi : i ≤ p.len) :
    WP isa (expTail W.code) t (RunInv p p.len ((8*(p.len-i))%5)) := by
  obtain ⟨s,mi,X,Xc,bs,hI,hw,hw',hR,hL,hL',hr,hb,ho⟩ := h
  refine WP.mono (expTail_ok W hw hw' hR (by omega_using [hL, hL']) (by omega_using [hi, hL]) hr hb ho hI) fun u hu => ?_
  exact ⟨s,mi,X,Xc,bs,by simpa only [hL] using hu,hw,hw',hR,hL,hL',hr,hb,ho⟩

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! Batch and trailing-byte bodies have public source addresses and control. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (loadGroup appliedBatch appliedGroup groupBody tailBody)

theorem loadGroup_ready {p : RunPub} {i : Nat} {s : State} (hi : i+5 ≤ p.len)
    (h : RunInv p i 0 s) : WP isa (.block loadGroup) s (GroupPre p.ws) := by
  obtain ⟨s0,mi,X,Xc,bs,hI,hw,hw',hR,hL,_,hr,hb,ho⟩ := h
  have hi' : i+5 ≤ bs.length := by omega_using [hi, hL]
  have hb5 : 5 ≤ (bs.drop i).length := by simp only [List.length_drop]; omega_using [hi, hL]
  have hr5 : ∀ j < 5, InRegions (s.rd ++ s.wr) ((p.ep + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) 1 := by
    intro j hj
    rw [hI.keep.rd,hI.keep.wr,BitVec.add_assoc,ofNat_add_ofNat]
    exact hr (i+j) (by omega_using [hi, hL, hj])
  have hb' : ∀ j (hj : j < 5), s.mem ((p.ep + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) =
      (bs.drop i)[j]'(by simp only [List.length_drop]; omega_using [hi, hL, hj]) := by
    intro j hj
    rw [BitVec.add_assoc,ofNat_add_ofNat,List.getElem_drop]
    exact hI.source hb ho (by omega_using [hi, hL, hj])
  refine WP.mono (loadGroup_ok hI.ctx hb5 hI.exp hI.idx hr5 hb') fun t ⟨hm,kt⟩ => ?_
  have out := writeW_outside s.mem (off p.ws.B p.ws.o) (d := 8 * Crt.sV)
    (BitVec.ofNat 64 (pre (bs.drop i) 5)) (by decide)
  rw [← hm] at out
  have ft : Frm (off p.ws.B p.ws.o) (crtWinRanges p.ws.wx) s.mem t.mem :=
    Frm.of_outside out (by simp [crtWinRanges])
  obtain ⟨E,v,_,_,_,hy,_⟩ := hI.pending
  have ey : wv t.mem (off p.ws.B p.ws.o) (slot p.ws.wx aY) p.ws.wx =
      wv s.mem (off p.ws.B p.ws.o) (slot p.ws.wx aY) p.ws.wx :=
    out.wv (by have := hdr_lt_slot p.ws.wx aY (show Crt.sV < 32 by decide); omega_using [this]) (by
      have := hI.ctx.good.scr.nowrap
      have := slot_le (w := p.ws.wx) (show aY < 8 by decide)
      omega_arith)
  exact ⟨mi,X,Xc,pre (bs.drop i) 5,hI.ctx.of_win ft kt.wr (kt.gpr .x0 (by decide)),
    hI.tab.of_win ft hI.ctx.scrT.nowrap,ey.symm ▸ hy,hw,hw',hR,
    by have := pre_lt (bs.drop i) hb5; omega_using [this],by rw [hm,word_writeW_self]⟩

theorem appliedGroup_ready (W : Window) (n : Nat) (hn : n ≤ 8) {p : XPub} {s : State}
    (h : GroupPre p s) : WP isa (appliedGroup W.code n) s (GroupPre p) := by
  induction n generalizing s with
  | zero => exact WP.block_nil h
  | succ n ih =>
    exact WP.seq (WP.mono (appliedStep_post W (5*n) (by omega_using [hn]) h) fun _ h => ih (by omega_using [hn]) h)

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
  have hi' : i < bs.length := by omega_using [hi, hL]
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

end

end

/-! ### `Bignum.AArch64.CrtWindowHeadCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowBuildCT`, which only this module used -/

section

/-! Constant-time construction of the 32-entry table. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## The table -/

/-- `toEnt a` into entry `q.2`: its bases, as the header gives them. -/
def EntP (a : Nat) (q : XPub × Nat) (s : State) : Prop :=
  XCtx q.1 s ∧ word s.mem (off q.1.B q.1.o) (8 * Crt.sEnt) = off (off q.1.B q.1.o) (slot q.1.wx (8 + q.2)) ∧
    q.2 < 32 ∧ a < 8

/-- `toEnt a`'s bases. -/
def EntB (a : Nat) (q : XPub × Nat) (s : State) : Prop :=
  s.gpr .x12 = BitVec.ofNat 64 q.1.wx ∧ s.gpr .x16 = off (off q.1.B q.1.o) (slot q.1.wx a) ∧
    s.gpr .x17 = off (off q.1.B q.1.o) (slot q.1.wx (8 + q.2))

theorem pins_entB (a : Nat) : Pins (EntB a) [.x12, .x16, .x17] := by
  intro q s₁ s₂ ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]

/-- `toEnt a`'s loads, in the workspace at `P`. -/
theorem toEntHd_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : TableCtx t P wx minv X Xc) {a e : Nat} (ha : a < 8) (he : word t.mem P (8 * Crt.sEnt) = off P e) :
    WP isa (.block [ldh .x12 sW, ldh .x16 (sArr a), ldh .x17 Crt.sEnt]) t fun t' =>
      t'.gpr .x12 = BitVec.ofNat 64 wx ∧ t'.gpr .x16 = off P (slot wx a) ∧ t'.gpr .x17 = off P e :=
  WP.mono (WP.keep [.x12, .x16, .x17] (Q := fun t' => t'.gpr .x12 = BitVec.ofNat 64 wx ∧
      t'.gpr .x16 = off P (slot wx a) ∧ t'.gpr .x17 = off P e)
    (by brun [hc.good.x0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt ha),
      hdr_enc (show Crt.sEnt < 32 by decide), hc.ld (i := sArr a) (sArr_lt ha), hc.ld (i := Crt.sEnt) (by decide),
      hc.ld (i := sW) (by decide), hc.good.hdr.harr a ha, he, hc.good.hdr.hw]) rfl rfl rfl) fun _ h => h.1

/-- `toEnt a` leaks the same in runs with the same workspace and entry,
given that the taint analysis checks its loads from `x0`. -/
theorem toEnt_ct {a : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x12 sW, ldh .x16 (sArr a), ldh .x17 Crt.sEnt])
      hc).isSome = true) :
    RelCT isa (Two (EntP a)) (seqs (toEnt a)) fun _ _ => True := by
  unfold toEnt
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := EntB a) [.x0] (pins_x0B (fun q : XPub × Nat => off q.1.B q.1.o)
    fun _ _ h => h.1.x0) hT fun q s ⟨⟨minv, X, Xc, hc, _⟩, he, hj, ha⟩ => ?_)
    (two_taint [.x12, .x16, .x17] (pins_entB a) (by taint_decide))
  exact WP.mono (toEntHd_ok hc ha he) fun _ h => h

/-- After `i` of the table's products, in the workspace of `p`. -/
def BldI (p : XPub) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc : Nat), BuildInv t₀ (off p.B p.o) p.wx minv X Xc False 0 i s ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.wx)) X ∧ Xc < X

/-- After the product `i`: the entry `i + 1` in `sEnt`. -/
def BldM (q : XPub × Nat) (s : State) : Prop :=
  XCtx q.1 s ∧ word s.mem (off q.1.B q.1.o) (8 * Crt.sEnt) = off (off q.1.B q.1.o) (slot q.1.wx (8 + (q.2 + 1))) ∧
    q.2 < 30

/-- `sEnt` up from entry `j` keeps the context. -/
theorem nextEnt_post {p : XPub} {j : Nat} {s : State} (h : XCtx p s)
    (he : word s.mem (off p.B p.o) (8 * Crt.sEnt) = off (off p.B p.o) (slot p.wx (8 + j))) :
    WP isa nextEnt s fun t => XCtx p t ∧
      word t.mem (off p.B p.o) (8 * Crt.sEnt) = off (off p.B p.o) (slot p.wx (8 + (j + 1))) := by
  obtain ⟨minv, X, Xc, hc, hXN, hw, hw'⟩ := h
  refine WP.mono (nextEnt_ok hc hw' he) fun t ⟨hm, k⟩ => ?_
  have o := writeW_outside s.mem (off p.B p.o) (d := 8 * Crt.sEnt)
    (off (off p.B p.o) (slot p.wx (8 + j) + 8 * (p.wx + 2))) (by decide)
  rw [← hm] at o
  exact ⟨⟨minv, X, Xc, hc.of_frm (Frm.of_outside o (by simp [VG.Proof.Bignum.CrtWindowFive.crtExpRanges, crtWinRanges])) k.wr
    (k.gpr .x0 (by decide)), hXN, hw, hw'⟩, by rw [hm, word_writeW_self, ← slot_succ]; rfl⟩

/-- A product of the table's build leaks the same in runs with the same workspace. -/
theorem buildBody_ct (M : Mont) :
    RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 30 ∧ BldI q.1 q.2 s)
      (seqs (tabBody M.mm)) fun _ _ => True := by
  -- `T := T Xc`.
  have mmPart : RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 30 ∧ BldI q.1 q.2 s) (M.mm Crt.aT Crt.aT Crt.aXc)
      (Two BldM) := by
    refine two_post (two_map (fun q : XPub × Nat => q.1.ws)
      (fun _ _ ⟨_, _, minv, _, _, hI, _⟩ => ⟨minv, hI.ctx.good, Nat.le_refl _⟩)
      (M.ct (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) (by unfold MmUse; decide)))
      fun q s ⟨hi, t₀, minv, X, Xc, hI, hw, hw', hR, hXN⟩ => ?_
    have hc := hI.ctx
    refine WP.mono (M.mm_ok (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) hc.good (Nat.le_refl _) hw (by omega_arith)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.x, hc.n]; exact hXN)) fun t ⟨_, _, _, ha, k⟩ => ?_
    have f : Frm (off q.1.B q.1.o) (VG.Proof.Bignum.CrtWindowFive.buildRanges q.1.wx) s.mem t.mem := Frm.of_arrays ha (by simp [VG.Proof.Bignum.CrtWindowFive.buildRanges])
    exact ⟨⟨minv, X, Xc, hc.of_frm (f.mono (VG.Proof.Bignum.CrtWindowFive.buildRanges_sub q.1.wx)) k.wr (k.gpr .x0 (by decide)), hXN, hw, hw'⟩,
      by rw [ha.hslot (by decide)]; exact hI.ent, hi⟩
  -- `sEnt` up.
  have entPart : RelCT isa (Two BldM) nextEnt (Two fun (q : XPub × Nat) s => EntP Crt.aT (q.1, q.2 + 2) s) :=
    two_post (x0_ct (fun q : XPub × Nat => off q.1.B q.1.o) (fun _ _ h => h.1.x0) (by taint_decide))
      fun q s ⟨hx, he, hi⟩ => WP.mono (nextEnt_post hx he) fun t ⟨hx', he'⟩ =>
        ⟨hx', he', by simp only; omega_arith, by decide⟩
  -- Entry `i + 2 := T`, the count.
  have restPart : RelCT isa (Two fun (q : XPub × Nat) s => EntP Crt.aT (q.1, q.2 + 2) s)
      (seqs (toEnt Crt.aT ++ [.block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]]))
      fun _ _ => True := by
    refine RelCT.seqs_append (by simp [toEnt]) (by simp) (RelCT.seq (two_post (Ψ := fun q t =>
      t.gpr .x0 = off q.1.B q.1.o) (two_map (fun q : XPub × Nat => (q.1, q.2 + 2)) (fun _ _ h => h)
        (toEnt_ct (by taint_decide))) fun q s ⟨⟨minv, X, Xc, hc, _, hw, hw'⟩, he, hj, ha⟩ =>
      WP.mono (toEnt_ok hc hw hw' ha hj he) fun t ⟨_, _, k⟩ => (k.gpr .x0 (by decide)).trans hc.good.x0) ?_)
    simp only [seqs]
    exact x0_ct (fun q : XPub × Nat => off q.1.B q.1.o) (fun _ _ h => h) (by taint_decide)
  unfold tabBody
  refine RelCT.seqs_append (by simp) (by simp [toEnt]) (RelCT.seq ?_ restPart)
  simp only [seqs]
  exact RelCT.seq mmPart entPart

/-- `tabBuild_ok`'s hypotheses, for the bounds. -/
def TPre (p : XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc : Nat), TableCtx s (off p.B p.o) p.wx minv X Xc ∧ Xc < X ∧
    wv s.mem (off p.B p.o) (slot p.wx aY) p.wx < X ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    Nat.Coprime (2 ^ (64 * p.wx)) X

theorem toEnt_post {a : Nat} {q : XPub × Nat} {s : State} (h : EntP a q s) :
    WP isa (seqs (toEnt a)) s fun t => XCtx q.1 t ∧
      ∀ k < 32, word t.mem (off q.1.B q.1.o) (8 * k) = word s.mem (off q.1.B q.1.o) (8 * k) := by
  obtain ⟨⟨minv, X, Xc, hc, hXN, hw, hw'⟩, he, hj, ha⟩ := h
  have hn := hc.scrT.nowrap
  have hE := VG.Proof.Bignum.CrtWindowFive.ent32_le q.1.wx hj
  have hE8 := slot_mono q.1.wx (show 8 ≤ 8 + q.2 by omega_arith)
  refine WP.mono (toEnt_ok hc hw hw' ha hj he) fun t ⟨_, o, k⟩ => ⟨⟨minv, X, Xc, hc.of_frm
    (Frm.of_outside (o.mono (o' := slot q.1.wx 8) (n' := VG.Proof.Bignum.CrtWindowFive.tabBytes32 q.1.wx) hE8 (by omega_arith)) (by simp [VG.Proof.Bignum.CrtWindowFive.crtExpRanges]))
    k.wr (k.gpr .x0 (by decide)), hXN, hw, hw'⟩, fun k hk => ?_⟩
  exact o.word (by have := hdr_lt_slot q.1.wx (8 + q.2) hk; omega_arith) (by omega_arith)

/-- The table's first entries leak the same in runs with the same workspace. -/
theorem tabPre_ct : RelCT isa (Two TPre) (seqs tabPre) fun _ _ => True := by
  unfold tabPre
  refine RelCT.seqs_append (by simp) (by simp [toEnt]) ?_
  simp only [seqs]
  -- The base.
  refine RelCT.seq (two_post (Ψ := fun p s => EntP aY (p, 0) s)
    (x0_ct (fun p : XPub => off p.B p.o) (fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.x0) (by taint_decide))
    fun p s ⟨minv, X, Xc, hc, hXN, hY, hw, hw', hR⟩ => ?_) ?_
  · refine WP.mono (tabInit_ok hc hw') fun t ⟨hm, k⟩ => ?_
    have o1 := writeW_outside s.mem (off p.B p.o) (d := 8 * Crt.sTab) (off (off p.B p.o) (slot p.wx 8)) (by decide)
    have o2 := writeW_outside (s.mem.writeW (off (off p.B p.o) (8 * Crt.sTab)) (off (off p.B p.o) (slot p.wx 8)))
      (off p.B p.o) (d := 8 * Crt.sEnt) (off (off p.B p.o) (slot p.wx 8)) (by decide)
    rw [← hm] at o2
    have f : Frm (off p.B p.o) (VG.Proof.Bignum.CrtWindowFive.buildRanges p.wx) s.mem t.mem :=
      (Frm.of_outside o1 (by simp [VG.Proof.Bignum.CrtWindowFive.buildRanges])).trans (Frm.of_outside o2 (by simp [VG.Proof.Bignum.CrtWindowFive.buildRanges]))
    exact ⟨⟨minv, X, Xc, hc.of_frm (f.mono (VG.Proof.Bignum.CrtWindowFive.buildRanges_sub p.wx)) k.wr (k.gpr .x0 (by decide)), hXN, hw, hw'⟩,
      by rw [hm, word_writeW_self]; rfl, by simp only; omega_arith, by decide⟩
  -- `T_0 := Y`.
  refine RelCT.seqs_append (by simp [toEnt]) (by simp) (RelCT.seq (two_post
    (Ψ := fun p s => XCtx p s ∧ word s.mem (off p.B p.o) (8 * Crt.sEnt) = off (off p.B p.o) (slot p.wx (8 + 0)))
    (two_map (fun p : XPub => (p, 0)) (fun _ _ h => h) (toEnt_ct (by taint_decide))) fun p s h =>
      WP.mono (toEnt_post h) fun t ⟨hx, hh⟩ => ⟨hx, by rw [hh _ (by decide)]; exact h.2.1⟩) ?_)
  refine RelCT.seqs_append (by simp) (by simp [toEnt]) ?_
  simp only [seqs]
  -- `sEnt` up.
  refine RelCT.seq (two_post (Ψ := fun p s => EntP Crt.aXc (p, 1) s)
    (x0_ct (fun p : XPub => off p.B p.o) (fun _ _ h => h.1.x0) (by taint_decide))
    fun p s ⟨hx, he⟩ => WP.mono (nextEnt_post hx he) fun t ⟨hx', he'⟩ => ⟨hx', he', show 1 < 32 by decide, by decide⟩) ?_
  -- `T_1 := Xc`.
  refine RelCT.seqs_append (by simp [toEnt]) (by simp [copyArr]) (RelCT.seq (two_post
    (Ψ := fun p s => XCtx p s) (two_map (fun p : XPub => (p, 1)) (fun _ _ h => h) (toEnt_ct (by taint_decide)))
    fun p s h => WP.mono (toEnt_post h) fun t ⟨hx, _⟩ => hx) ?_)
  -- `T := Xc`, the count.
  refine RelCT.seqs_append (by simp [copyArr]) (by simp) (RelCT.seq (two_post
    (Ψ := fun p t => t.gpr .x0 = off p.B p.o) (two_map (fun p : XPub => p.ws) (fun _ _ h => h.goodW)
      (copyArr_ct (by decide) (by decide) (by taint_decide))) fun p s ⟨minv, X, Xc, hc, _, hw, hw'⟩ =>
    WP.mono (copyArr_ok hc.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := Crt.aT) (a := Crt.aXc)
      (by decide) (by decide) (by decide)) fun t ⟨_, _, k⟩ => (k.gpr .x0 (by decide)).trans hc.good.x0) ?_)
  simp only [seqs]
  exact x0_ct (fun p : XPub => off p.B p.o) (fun _ _ h => h) (by taint_decide)

/-- The table's build leaks the same in runs with the same workspace. -/
theorem tabBuild_ct (M : Mont) : RelCT isa (Two TPre) (seqs (VG.Impl.Rsa.AArch64.WindowFive.tabBuild32 M.mm)) fun _ _ => True := by
  rw [tabBuild_eq]
  refine RelCT.seqs_append (by simp [tabPre]) (by simp) (RelCT.seq (two_post (Ψ := fun p s => 0 < 30 ∧ BldI p 0 s)
    tabPre_ct fun p s ⟨minv, X, Xc, hc, hXN, hY, hw, hw', hR⟩ =>
      WP.mono (tabPre_ok (Q := False) (x := 0) hc hw hw' hXN False.elim hY False.elim) fun t hI =>
        ⟨by decide, s, minv, X, Xc, hI, hw, hw', hR, hXN⟩) ?_)
  simp only [seqs, tabLoop]
  exact (two_loop (Φ := BldI) (Ψ := fun _ _ => True) (fun _ => 30) (buildBody_ct M)
    fun p i s hi ⟨t₀, minv, X, Xc, hI, hw, hw', hR, hXN⟩ =>
      WP.mono (buildStep_ok M hw hw' hR hXN False.elim hi hI) fun s' ⟨hI', hz⟩ =>
        ⟨eval_nz_count hi hz, fun _ => ⟨t₀, minv, X, Xc, hI', hw, hw', hR, hXN⟩, fun _ => trivial⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial


end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! The wider-table initializer shares only workspace and source layout between runs. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt (ldw)
open VG.Proof.MlKem.AArch64 (Keep)

def EPreWide (sp sl : Nat) (a : BPub) (s : State) : Prop :=
  EPre sp sl a s ∧ a.x.o + slot a.x.wx 8 + CrtWindowFive.tabBytes32 a.x.wx ≤ a.x.Z

theorem expInit_tpre {sp sl : Nat} {a : BPub} {s : State} (h : EPreWide sp sl a s) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.expInit sp sl) s (TPre a.x) := by
  obtain ⟨h,hwide⟩ := h
  obtain ⟨minv, X, x, y, eb, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, -, hyl, -, hsp, hsl, hep, hel, -⟩ := h
  have hT : Scr s (off a.x.B a.x.o) (slot a.x.wx 8 + CrtWindowFive.tabBytes32 a.x.wx) :=
    hc.scr.sub (by omega_using [hwide]) (by unfold slot hdrBytes; omega_using [])
  have hPn := hT.nowrap
  have hY0 := slot_le (w := a.x.wx) (show aY < 8 by decide)
  have hY1 := hdr_lt_slot a.x.wx aY (show 31 < 32 by decide)
  have hc₀ : TableCtx s (off a.x.B a.x.o) a.x.wx minv X (wv s.mem (off a.x.B a.x.o) (slot a.x.wx Crt.aXc) a.x.wx) :=
    ⟨hc.good, hT, hn, hinv, rfl⟩
  refine WP.mono (crtExpInit_ok hc hsp hsl hep hel) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := writeW_outside s.mem (off a.x.B a.x.o) (d := 8 * Crt.sExp) a.ptr (by decide)
  have o2 := writeW_outside (s.mem.writeW (off (off a.x.B a.x.o) (8 * Crt.sExp)) a.ptr) (off a.x.B a.x.o)
    (d := 8 * Crt.sExpLen) (BitVec.ofNat 64 eb.length) (by decide)
  have o3 := writeW_outside ((s.mem.writeW (off (off a.x.B a.x.o) (8 * Crt.sExp)) a.ptr).writeW
    (off (off a.x.B a.x.o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 eb.length)) (off a.x.B a.x.o) (d := 8 * Crt.sI)
    (BitVec.ofNat 64 0) (by decide)
  rw [← hm₁] at o3
  have f₁ : Frm (off a.x.B a.x.o) (CrtWindowFive.crtExpRanges a.x.wx) s.mem t₁.mem :=
    ((Frm.of_outside o1 (by simp [CrtWindowFive.crtExpRanges])).trans (Frm.of_outside o2 (by simp [CrtWindowFive.crtExpRanges]))).trans
      (Frm.of_outside o3 (by simp [CrtWindowFive.crtExpRanges]))
  refine ⟨minv, X, _, hc₀.of_frm f₁ k₁.wr (k₁.gpr .x0 (by decide)), hxl, ?_, hw2, by omega_arith,
    VG.Proof.Bignum.coprime_pow2 hodd _⟩
  rw [o3.wv (by unfold Crt.sI sFn at *; omega_arith) (by omega_arith), o2.wv (by unfold Crt.sExpLen sFn at *; omega_arith)
    (by omega_arith), o1.wv (by unfold Crt.sExp sFn at *; omega_arith) (by omega_arith)]
  exact hyl


theorem expInit_ct {sp sl : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0,.x5]) (.block [ldw .x3 .x5 sp,sth .x3 Crt.sExp,
      ldw .x3 .x5 sl,sth .x3 Crt.sExpLen,movi .x3 0,sth .x3 Crt.sI]) hc).isSome = true) :
    RelCT isa (Two (EPreWide sp sl)) (VG.Impl.Rsa.AArch64.WindowFive.expInit sp sl) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.expInit
  exact RelCT.block_append (l₁ := ([ldh .x5 Crt.sLink] : List Instr))
    (RelCT.seq (two_piece (Ψ := fun (a : BPub) t => t.gpr .x0 = off a.x.B a.x.o ∧ t.gpr .x5 = a.x.B) [.x0]
      (pins_x0B (fun a : BPub => off a.x.B a.x.o) fun a s (h : EPreWide sp sl a s) =>
        let ⟨_,_,_,_,_,ctx,_⟩ := h.1; ctx.x0) (by taint_decide)
      fun _ _ h => crtLink_ok h.1)
    (two_taint [.x0,.x5] (pins_of (fun a r => if r = .x0 then off a.x.B a.x.o else a.x.B)
      fun a s h r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) hT))

theorem expHead_ct (M : Mont) {sp sl : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0,.x5]) (.block [ldw .x3 .x5 sp,sth .x3 Crt.sExp,
      ldw .x3 .x5 sl,sth .x3 Crt.sExpLen,movi .x3 0,sth .x3 Crt.sI]) hc).isSome = true) :
    RelCT isa (Two (EPreWide sp sl)) (VG.Impl.Rsa.AArch64.WindowFive.expHead M.mm sp sl) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.expHead
  refine RelCT.seq (two_post (Ψ := fun a s => TPre a.x s) (expInit_ct hT)
    (fun _ _ h => expInit_tpre h)) ?_
  refine RelCT.seq (two_map (fun a : BPub => a.x) (fun _ _ h => h)
    (two_post (Ψ := fun (p : XPub) s => s.gpr .x0 = off p.B p.o) (tabBuild_ct M) ?_)) ?_
  · rintro p s ⟨mi,X,Xc,hctx,hxl,hyl,hw,hw',hR⟩
    exact WP.mono (tabBuild_ok M hctx hw hw' hR hxl (Q := False) (x := 0) False.elim hyl False.elim)
      fun t ⟨ct,_⟩ => ct.good.x0
  · exact two_map (fun p : XPub => off p.B p.o) (fun _ _ h => h) resetWindow_ct

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowGroupsCT`, which only this module used -/

section

/-! Complete groups iterate a public number of times. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (groupBody expGroups)

theorem groups_loop_ct (W : Window) :
    RelCT isa (Two fun p s => 0 < p.len/5 ∧ RunInv p 0 0 s)
      (.loop (groupBody W.code) (.nonzero .x .x9)) (fun _ _ => True) := by
  refine (two_loop (Φ := fun p j => RunInv p (5*j) 0) (Ψ := fun p => RunInv p (5*(p.len/5)) 0)
    (fun p : RunPub => p.len/5) ?_ ?_).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  · exact two_map (fun p : RunPub × Nat => (p.1,5*p.2))
      (fun _ _ h => ⟨by dsimp; omega,h.2⟩) (groupBody_ct W)
  · intro p j s hj hs
    refine WP.mono (hs.groupStep W (by omega_using [hj])) fun t ⟨ht,h9⟩ => ?_
    have hnext : RunInv p (5*(j+1)) 0 t := by simpa only [Nat.mul_add,Nat.mul_one] using ht
    refine ⟨?_,fun _ => hnext,fun he => by simpa only [he] using hnext⟩
    change some (!(t.gpr .x9 == 0)) = some (decide (j+1 < p.len/5))
    rw [h9]
    by_cases he : 5*j+10 ≤ p.len
    · simp only [he,ite_true,show j+1 < p.len/5 by omega_using [he],decide_true]; rfl
    · simp only [he,ite_false,show ¬ j+1 < p.len/5 by omega_using [he],decide_false]; rfl

def GroupsReady (p : RunPub) (s : State) : Prop :=
  RunInv p 0 0 s ∧ s.gpr .x9 = if 5 ≤ p.len then 1 else 0

theorem expGroups_ct (W : Window) :
    RelCT isa (Two fun p => RunInv p 0 0) (expGroups W.code) (fun _ _ => True) := by
  unfold expGroups
  refine RelCT.seq (two_post (Ψ := GroupsReady)
    (x0_ct (fun p : RunPub => off p.ws.B p.ws.o) (fun _ _ h => h.x0) (by taint_decide))
    (fun _ _ h => WP.mono (h.haveFive (Nat.zero_le _)) fun _ ht => ⟨ht.1,by simpa only [Nat.zero_add] using ht.2⟩)) ?_
  refine two_ite ?_ ?_ ?_
  · intro p s t hs ht
    change some (!(s.gpr .x9 == 0)) = some (!(t.gpr .x9 == 0))
    rw [hs.2,ht.2]
  · exact two_map id (fun p s ⟨hs,he⟩ => ⟨by
      change 0 < p.len/5
      by_contra hz
      have hn : ¬ 5 ≤ p.len := by omega_using [hz]
      change some (!(s.gpr .x9 == 0)) = some true at he
      rw [hs.2,ite_eq_right hn] at he
      contradiction,hs.1⟩) (groups_loop_ct W)
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (hc := .block []) rfl

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowTailsCT`, which only this module used -/

section

/-! The trailing-byte loop depends on public length, never exponent bits. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (tailBody expTail)

theorem tails_loop_ct (W : Window) :
    RelCT isa (Two fun (p : RunPub × Nat) s => 0 < p.1.len-p.2 ∧ RunInv p.1 p.2 0 s)
      (.loop (tailBody W.code) (.nonzero .x .x3)) (fun _ _ => True) := by
  refine (two_loop (Φ := fun (p : RunPub × Nat) j => RunInv p.1 (p.2+j) ((8*j)%5))
    (Ψ := fun _ _ => True) (fun p : RunPub × Nat => p.1.len-p.2) ?_ ?_).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)
  · exact two_map (fun p : (RunPub × Nat) × Nat => (p.1.1,p.1.2+p.2,(8*p.2)%5))
      (fun _ _ h => ⟨by dsimp; omega,h.2⟩) (tailBody_ct W)
  · intro p j s hj hs
    have hL : p.1.len < 2 ^ 64 := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,hL,_⟩ := hs
      exact hL
    refine WP.mono (hs.tailStep W (by omega_using [hj])) fun t ⟨ht,h3⟩ => ?_
    refine ⟨?_,?_,fun _ => trivial⟩
    · exact eval_nz_count hj (by rw [h3,cnt_ne (by omega_using [hL])]; omega_using [hj])
    · intro _
      have hb : ((8*j)%5+8)%5 = (8*(j+1))%5 := by omega_using []
      simpa only [hb,Nat.add_assoc] using ht

def TailsReady (p : RunPub × Nat) (s : State) : Prop :=
  p.2 ≤ p.1.len ∧ RunInv p.1 p.2 0 s ∧ s.gpr .x3 = BitVec.ofNat 64 (p.1.len-p.2)

theorem expTail_ct (W : Window) :
    RelCT isa (Two fun (p : RunPub × Nat) s => p.2 ≤ p.1.len ∧ RunInv p.1 p.2 0 s)
      (expTail W.code) (fun _ _ => True) := by
  unfold expTail
  refine RelCT.seq (two_post (Ψ := TailsReady)
    (x0_ct (fun p : RunPub × Nat => off p.1.ws.B p.1.ws.o) (fun _ _ h => h.2.x0) (by taint_decide))
    (fun _ _ h => WP.mono (h.2.remaining h.1) fun _ h' => ⟨h.1,h'⟩)) ?_
  refine two_ite ?_ ?_ ?_
  · intro p s t hs ht
    change some (!(s.gpr .x3 == 0)) = some (!(t.gpr .x3 == 0))
    rw [hs.2.2,ht.2.2]
  · exact two_map id (fun p s ⟨hs,he⟩ => ⟨by
      change 0 < p.1.len-p.2
      by_contra hz
      have hn : p.1.len-p.2 = 0 := by omega_using [hz]
      change some (!(s.gpr .x3 == 0)) = some true at he
      rw [hs.2.2,hn] at he
      contradiction,hs.2.1⟩) (tails_loop_ct W)
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (hc := .block []) rfl

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowRunCT`, which only this module used -/

section

/-! Constant time for the complete exponent, including both tails. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (expRun)

theorem expRun_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p => RunInv p 0 0) (expRun W.code M.mm S.code) (fun _ _ => True) := by
  unfold expRun
  refine RelCT.seq (two_post (Ψ := fun p => RunInv p (5*(p.len/5)) 0)
    (expGroups_ct W) (fun _ _ h => h.groups W)) ?_
  refine RelCT.seq (two_post (Ψ := fun p => RunInv p p.len ((8*(p.len-5*(p.len/5)))%5))
    (two_map (fun p : RunPub => (p,5*(p.len/5)))
      (fun _ _ h => ⟨by dsimp; omega_using [],h⟩) (expTail_ct W))
    (fun _ _ h => h.tails W (by omega_using []))) ?_
  exact two_map (fun p : RunPub => (p.ws,(8*(p.len-5*(p.len/5)))%5))
    (fun _ _ h => h.finish) (finish_ct M S)

end VG.Proof.Bignum.AArch64.WindowFive

end

end


/-! Constant time for wider-table prime exponentiation under the existing key bounds. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt (ldw)

def runPub (a : BPub) : RunPub := ⟨a.x,a.ptr,a.len⟩

theorem expHead_post (M : Mont) {sp sl : Nat} {a : BPub} {s : State}
    (h : EPreWide sp sl a s) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.expHead M.mm sp sl) s (RunInv (runPub a) 0 0) := by
  obtain ⟨h,hwide⟩ := h
  obtain ⟨mi,X,x,y,bs,hctx,hw2,hwx,hw30,hn,hinv,hodd,hxl,_,hyl,_,hsp,hsl,hep,hel,hL,_,hL2,he⟩ := h
  have hT : Scr s (off a.x.B a.x.o) (slot a.x.wx 8 + CrtWindowFive.tabBytes32 a.x.wx) :=
    hctx.scr.sub (by omega_using [hwide]) (by unfold slot hdrBytes; omega_using [])
  have hout : ∀ i < bs.length, slot a.x.wx 8 + CrtWindowFive.tabBytes32 a.x.wx ≤
      ofs (off a.x.B a.x.o) (a.ptr + BitVec.ofNat 64 i) := by
    intro i hi
    have := he.out i hi
    have hn := hctx.scr.nowrap
    have hp := hT.nowrap
    have hslot : 0 < slot a.x.wx 8 := by unfold slot hdrBytes; omega_using []
    rcases ofs_rebase a.x.B (a.ptr + BitVec.ofNat 64 i) (o := a.x.o) (by omega_using [hwide, hn, hslot]) with ⟨_,h2⟩ | ⟨h1,_⟩
    · omega_using [hwide, this, h2]
    · omega_using [hwide, this, h1]
  refine WP.mono (expHead_ok M (Q := False) (x := 0) hctx hT hw2 hwx hw30 hn hinv hodd
    hxl False.elim hyl False.elim hsp hsl hep hel) fun t ht => ?_
  exact ⟨s,mi,X,_,bs,ht,hw2,by dsimp [runPub]; omega_using [hwx, hw30],VG.Proof.Bignum.coprime_pow2 hodd _,hL,by dsimp [runPub]; omega,
    he.rd,he.val,hout⟩

theorem expLoop_ct (W : Window) (M : Mont) (S : Selector) {sp sl : Nat}
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0,.x5]) (.block [ldw .x3 .x5 sp,sth .x3 Crt.sExp,
      ldw .x3 .x5 sl,sth .x3 Crt.sExpLen,movi .x3 0,sth .x3 Crt.sI]) hc).isSome = true) :
    RelCT isa (Two (EPreWide sp sl))
      (VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code sp sl) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.expLoop
  exact RelCT.seq (two_post (Ψ := fun a => RunInv (runPub a) 0 0) (expHead_ct M hT)
    (fun _ _ h => expHead_post M h)) (two_map runPub (fun _ _ h => h) (expRun_ct W M S))

end VG.Proof.Bignum.AArch64.WindowFive
