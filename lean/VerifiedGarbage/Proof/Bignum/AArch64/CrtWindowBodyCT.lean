module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunContext
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoadGroup
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoadGroup
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTails
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailByte
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingMath
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTakeBit
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailByte
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTakeBit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowDigit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedStep
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCoreCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowDigit
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedStep
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCoreCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore

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
