module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStepCT
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMont
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStepCT
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowShared
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedStep
import VerifiedGarbage.Proof.Bignum.CrtWindowRelation

/-! ### `Bignum.AArch64.WindowSharedWork`, which the modules that import this one used -/

section

/-! ### `Bignum.AArch64.WindowSharedLoop`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

structure LoopInv (s : State) (P : Addr) (w : Nat) (mi : BitVec 64) (X Xc j : Nat) (t : State) : Prop where
  ctx : TableCtx t P w mi X Xc
  value : wv t.mem P (slot w aY) w * (2^(64*w))^(2^j-1) % X =
    (wv s.mem P (slot w aY) w)^(2^j) % X
  bit : word t.mem P (8*Crt.sBit) = BitVec.ofNat 64 (5-j)
  hdr : ∀ i < 32, i ≠ Crt.sBit → word t.mem P (8*i) = word s.mem P (8*i)
  frame : Frm P (crtWinRanges w) s.mem t.mem
  keep : Keep WindowRaw.regs s t

theorem loop_step {s t : State} {P : Addr} {w j : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hw : 16 ≤ w) (hw' : w < 2^30) (hmod : w % 8 = 0) (hj : j < 5)
    (hI : LoopInv s P w mi X Xc j t) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.step t fun u =>
      LoopInv s P w mi X Xc (j+1) u ∧ ((u.gpr .x3).toNat ≠ 0 ↔ j+1 ≠ 5) := by
  refine WP.mono (step_ok hI.ctx hw hw' hmod hj hI.bit hI.value)
    fun u ⟨cu,hu,hb,h3,hh,hf,hk⟩ => ⟨?_,?_⟩
  · refine ⟨cu,?_,hb,fun i hi hb' => (hh i hi hb').trans (hI.hdr i hi hb'),
      hI.frame.trans hf,(hI.keep.trans hk).mono (by decide)⟩
    have he : 2*(2^j-1)+1 = 2^(j+1)-1 := by
      have := Nat.two_pow_pos j
      rw [Nat.pow_succ]
      omega_using [this]
    have ep : (wv s.mem P (slot w aY) w ^ (2^j))^2 =
        wv s.mem P (slot w aY) w ^ (2^(j+1)) := by
      rw [← Nat.pow_mul,← Nat.pow_succ]
    rw [he,ep] at hu
    exact hu
  · rw [h3,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 5-(j+1) < 2^64 by omega_using [])]
    omega_using [hj]

theorem squares_ok {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : 16 ≤ w) (hw' : w < 2^30) (hmod : w % 8 = 0)
    (hb : word s.mem P (8*Crt.sBit) = BitVec.ofNat 64 5) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.squares s fun t =>
      TableCtx t P w mi X Xc ∧
      wv t.mem P (slot w aY) w * (2^(64*w))^31 % X =
        (wv s.mem P (slot w aY) w)^32 % X ∧
      (∀ i < 32, i ≠ Crt.sBit → word t.mem P (8*i) = word s.mem P (8*i)) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep WindowRaw.regs s t := by
  have h0 : LoopInv s P w mi X Xc 0 s :=
    ⟨hc,by simp,hb,fun _ _ _ => rfl,Frm.refl _ _ _,Keep.refl _ _⟩
  exact WP.mono (count_loop (n := 5) (by decide) (LoopInv s P w mi X Xc)
    (fun j hj t hi => loop_step hw hw' hmod hj hi) h0)
    fun _ hi => ⟨hi.ctx,hi.value,hi.hdr,hi.frame,hi.keep⟩

end VG.Proof.Bignum.AArch64.WindowShared

end

end

/-! ### `Bignum.AArch64.WindowSharedCore`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

theorem core_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X False 0)
    (hw : 16 ≤ w) (hw' : w < 2^30) (hmod : w % 8 = 0)
    (hb : word s.mem P (8*Crt.sBit) = BitVec.ofNat 64 5)
    (hv : v < 32) (hnib : word s.mem P (8*Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.core s fun t =>
      TableCtx t P w mi X Xc ∧ wv t.mem P (slot w aY) w < X ∧
      wv t.mem P (slot w aY) w * (2^(64*w))^32 % X =
        wv s.mem P (slot w aY) w ^ 32 * wv s.mem P (slot w (8+v)) w % X ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep WindowRaw.regs s t ∧
      (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → k ≠ Crt.sBit →
        word t.mem P (8*k) = word s.mem P (8*k)) := by
  unfold VG.Impl.Rsa.AArch64.WindowShared.core
  refine WP.seq (WP.mono (squares_ok hc hw hw' hmod hb) fun a ⟨ca,va,ha,fa,ka⟩ => ?_)
  have ta := ht.of_win fa hc.scrT.nowrap
  have et : wv a.mem P (slot w (8+v)) w = wv s.mem P (slot w (8+v)) w :=
    fa.wv_eq (fun r hr => by have := crtWinRanges_ent w v r hr; omega_using [this])
      (by have := CrtWindowFive.ent32_le w hv; have := hc.scrT.nowrap; omega_arith)
  refine WP.seq (WP.mono (WindowVector.blocked_ok ca (by omega_using [hw]) hw' hmod hv ta.tab
    (by rw [ha _ (by decide) (by decide)]; exact hnib)) fun b ⟨cb,tb,fb,kb⟩ => ?_)
  have ey := WindowFive.selection_keeps_y fb ca.good.scr.nowrap
  refine WP.mono (WindowArithmetic.product_ok (o := aY) (a := aY) (b := Crt.aT)
    cb.good.scr cb.good.x0 cb.good.hdr (Nat.le_refl _) hw (by omega_using [hw']) hmod
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) cb.inv (by rw [cb.n,tb]; exact ta.lt v hv))
    fun t ⟨yt,vt,hat,kt⟩ => ?_
  rw [cb.n] at yt vt
  have ft : Frm P (crtWinRanges w) b.mem t.mem := Frm.of_arrays hat (by simp [crtWinRanges])
  have vb : wv b.mem P (slot w aY) w * (2^(64*w))^31 % X = wv s.mem P (slot w aY) w ^ 32 % X := by
    rw [ey]; exact va
  have result := CrtWindowFive.product_scale vt vb
  rw [tb,et] at result
  refine ⟨cb.of_win ft kt.wr (kt.gpr .x0 (by decide)),yt,result,
    (fa.trans (fb.mono (selRanges_sub w))).trans ft,
    ((ka.trans kb).trans kt).mono (by decide),?_⟩
  intro k hk he hj hb'
  rw [hat.hslot hk, fb.word_eq (fun r hr => by
    simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have := hdr_lt_slot w Crt.aT hk; simp only; omega_using [this]
    · simp only; omega_using [he]
    · simp only; omega_using [hj]) (by
      have := hdr_lt_slot w 8 hk
      have := ca.good.scr.nowrap
      omega_using [hk]), ha k hk hb']

end VG.Proof.Bignum.AArch64.WindowShared

end

end

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

theorem init_ok {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) :
    WP isa (.block [movi .x3 5, sth .x3 Crt.sBit]) s fun t =>
      (t.mem = s.mem.writeW (off P (8*Crt.sBit)) (BitVec.ofNat 64 5)) ∧ Keep [.x3] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [hc.good.x0,hdr_enc (show Crt.sBit < 32 by decide),hc.st (i := Crt.sBit) (by decide)]
  rfl

theorem work_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X False 0)
    (hw : 16 ≤ w) (hw' : w < 2^30) (hmod : w % 8 = 0)
    (hv : v < 32) (hnib : word s.mem P (8*Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.work s fun t =>
      TableCtx t P w mi X Xc ∧ wv t.mem P (slot w aY) w < X ∧
      wv t.mem P (slot w aY) w * (2^(64*w))^32 % X =
        wv s.mem P (slot w aY) w ^ 32 * wv s.mem P (slot w (8+v)) w % X ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep WindowRaw.regs s t ∧
      (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → k ≠ Crt.sBit →
        word t.mem P (8*k) = word s.mem P (8*k)) := by
  unfold VG.Impl.Rsa.AArch64.WindowShared.work
  refine WP.seq (WP.mono (init_ok hc) fun u ⟨hm,ku⟩ => ?_)
  have hout := writeW_outside s.mem P (d := 8*Crt.sBit) (BitVec.ofNat 64 5) (by decide)
  rw [← hm] at hout
  have fu : Frm P (crtWinRanges w) s.mem u.mem := Frm.of_outside hout (by simp [crtWinRanges])
  have cu := hc.of_win fu ku.wr (ku.gpr .x0 (by decide))
  have tu := ht.of_win fu hc.scrT.nowrap
  have read (j : Nat) (hj : slot w j+8*w ≤ slot w 8+CrtWindowFive.tabBytes32 w) :
      wv u.mem P (slot w j) w = wv s.mem P (slot w j) w :=
    hout.wv (by have := hdr_lt_slot w j (show Crt.sBit < 32 by decide); omega_using [this])
      (by have := hc.scrT.nowrap; omega_using [hj, this])
  refine WP.mono (core_ok cu tu hw hw' hmod (by rw [hm,word_writeW_self]) hv
    (by rw [hm,hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hnib))
    fun t ⟨ct,yt,vt,ft,kt,hh⟩ => ?_
  rw [read aY (by have := slot_le (w := w) (show aY < 8 by decide); omega_using [this]),
    read (8+v) (by have := CrtWindowFive.ent32_le w hv; omega_using [this])] at vt
  refine ⟨ct,yt,vt,fu.trans ft,(ku.trans kt).mono (by decide),?_⟩
  intro k hk he hj hb
  rw [hh k hk he hj hb,hm,hdrStore_hdr _ _ _ (by decide) hk (Ne.symm hb)]

end VG.Proof.Bignum.AArch64.WindowShared

end

end

/-! Select SIMD only for complete public-width tiles, with a scalar fallback:
for a table of 16 or 32 entries (`select_ok`, `select_ct`), and RSA's of 32
with its scalar selector (`selector`). -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff eval_zero eq_zero_iff)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx Selector)

def selected : Prog isa := VG.Impl.Rsa.AArch64.WindowSelectVector.select 32 Selector.scalar.code

/-! ## RSA's table of 32 entries -/

theorem selected_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hv : v < 32)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hN : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa selected s fun t => TableCtx t P w mi X Xc ∧
      wv t.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w ∧
      Frm P (selRanges w) s.mem t.mem ∧ Keep mmRegs s t :=
  WP.mono (select_ok (Or.inr rfl) (fun hu tab nib =>
      WP.mono (Selector.scalar.ok (TableCtx.ofC hu) hw hw' hv tab nib) fun _ ⟨ct,hy,hf,kt⟩ => ⟨ct.toC,hy,hf,kt⟩)
    hc.toC hw' hv ht hN) fun _ ⟨ct,hy,hf,kt⟩ => ⟨TableCtx.ofC ct,hy,hf,kt⟩

theorem selP_n {p : XPub} {s : State} (h : VG.Proof.Bignum.AArch64.WindowFive.SelP p s) : SelPn 32 p s := by
  obtain ⟨mi,X,Xc,v,hc,h⟩ := h
  exact ⟨mi,X,Xc,v,hc.toC,h⟩

theorem selP_of_n {p : XPub} {s : State} (h : SelPn 32 p s) : VG.Proof.Bignum.AArch64.WindowFive.SelP p s := by
  obtain ⟨mi,X,Xc,v,hc,h⟩ := h
  exact ⟨mi,X,Xc,v,TableCtx.ofC hc,h⟩

/-- `BlockPreN` for RSA's table of 32 entries. -/
def BlockPre (p : XPub) (s : State) : Prop := VG.Proof.Bignum.AArch64.WindowFive.SelP p s ∧ 8 ≤ p.wx

theorem blocked_ct : RelCT isa (Two BlockPre)
    (VG.Impl.Rsa.AArch64.WindowSelectVector.blocked 32) (fun _ _ => True) :=
  two_map id (fun _ _ ⟨⟨mi, X, Xc, v, hc, h⟩, hw⟩ => ⟨⟨mi, X, Xc, v, hc.toC, h⟩, hw⟩) (blockedN_ct (Or.inr rfl))

theorem selected_ct : RelCT isa (Two VG.Proof.Bignum.AArch64.WindowFive.SelP)
    selected (fun _ _ => True) :=
  two_map id (fun _ _ h => selP_n h)
    (select_ct (Or.inr rfl) (two_map id (fun _ _ h => selP_of_n h) Selector.scalar.ct))

def selector : Selector := ⟨selected,selected_ok,selected_ct⟩

end VG.Proof.Bignum.AArch64.WindowVector
