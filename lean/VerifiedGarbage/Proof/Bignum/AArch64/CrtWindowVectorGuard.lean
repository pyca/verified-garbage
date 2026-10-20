module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcGuard
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Select SIMD only for complete public-width tiles, with a scalar fallback. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff eval_zero eq_zero_iff)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx Selector)

def guard : List Instr := [ldh .x12 sW, .lsr .x .x3 .x12 3, movi .x4 7,
  .logic .and .x .x4 .x12 .x4]

def selected : Prog isa := VG.Impl.Rsa.AArch64.WindowSelectVector.select 32 Selector.scalar.code

theorem shr3_width {w : Nat} (hw : w < 2 ^ 64) :
    BitVec.ofNat 64 w >>> 3 = BitVec.ofNat 64 (w / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show w / 8 < 2 ^ 64 by omega)]

theorem guard_ok {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : w < 2 ^ 30) :
    WP isa (.block guard) s fun t =>
      (t.mem = s.mem ∧ t.gpr .x3 = BitVec.ofNat 64 (w / 8) ∧
        t.gpr .x4 = BitVec.ofNat 64 (w % 8)) ∧ Keep [.x12,.x3,.x4] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [guard, hc.good.x0, hdr_enc (show sW < 32 by decide), hc.ld (i := sW) (by decide),
    hc.good.hdr.hw, shr3_width (show w < 2 ^ 64 by omega)]
  exact BlockedRedc.mask7_ofNat (by omega)

theorem selected_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hv : v < 32)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hN : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa selected s fun t => TableCtx t P w mi X Xc ∧
      wv t.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w ∧
      Frm P (selRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold selected VG.Impl.Rsa.AArch64.WindowSelectVector.select
  refine WP.seq (WP.mono (guard_ok hc hw') fun u ⟨⟨hm,h3,h4⟩,ku⟩ => ?_)
  have ctx := hc.of_win (by rw [hm]; exact Frm.refl _ _ _) ku.wr (ku.gpr .x0 (by decide))
  have tab : word u.mem P (8 * Crt.sTab) = off P (slot w 8) := by rw [hm]; exact ht
  have nib : word u.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v := by rw [hm]; exact hN
  have slow : WP isa Selector.scalar.code u (fun t => TableCtx t P w mi X Xc ∧
      wv t.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w ∧
      Frm P (selRanges w) s.mem t.mem ∧ Keep mmRegs s t) := WP.mono (Selector.scalar.ok ctx hw hw' hv tab nib) fun t ⟨ct,hy,hf,kt⟩ =>
    ⟨ct,hm ▸ hy,hm ▸ hf,(ku.trans kt).mono (by decide)⟩
  by_cases fast : 8 ≤ w
  · refine WP.ite true (by rw [eval_nonzero,h3,ne_zero_iff,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show w / 8 < 2 ^ 64 by omega),decide_eq_true (show w / 8 ≠ 0 by omega)])
      (fun _ => ?_) (by simp)
    by_cases hd : w % 8 = 0
    · refine WP.ite true (by rw [eval_zero,h4,hd]; rfl) (fun _ => ?_) (by simp)
      exact WP.mono (blocked_ok ctx fast hw' hd hv tab nib) fun t ⟨ct,hy,hf,kt⟩ =>
        ⟨ct,hm ▸ hy,hm ▸ hf,(ku.trans kt).mono (by decide)⟩
    · exact WP.ite false (by rw [eval_zero,h4,eq_zero_iff,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show w % 8 < 2 ^ 64 by omega),decide_eq_false hd]) (by simp) (fun _ => slow)
  · exact WP.ite false (by rw [eval_nonzero,h3,show w / 8 = 0 by omega]; rfl) (by simp) (fun _ => slow)

structure GuardCtx (p : XPub) (s : State) : Prop where
  sel : VG.Proof.Bignum.AArch64.WindowFive.SelP p s
  width : s.gpr .x3 = BitVec.ofNat 64 (p.wx / 8)
  rem : s.gpr .x4 = BitVec.ofNat 64 (p.wx % 8)

theorem guard_ready {p : XPub} {s : State} (h : VG.Proof.Bignum.AArch64.WindowFive.SelP p s) :
    WP isa (.block guard) s (GuardCtx p) := by
  obtain ⟨mi,X,Xc,v,hc,hw,hw',hv,ht,hN⟩ := h
  refine WP.mono (guard_ok hc hw') fun u ⟨⟨hm,h3,h4⟩,ku⟩ => ?_
  exact ⟨⟨mi,X,Xc,v,hc.of_win (by rw [hm]; exact Frm.refl _ _ _) ku.wr
    (ku.gpr .x0 (by decide)),hw,hw',hv,hm ▸ ht,hm ▸ hN⟩,h3,h4⟩

theorem guard_width {p : XPub} {s : State} (h : GuardCtx p s)
    (ht : isa.eval (.nonzero .x .x3) s = some true) : 8 ≤ p.wx := by
  obtain ⟨_,_,_,_,_,_,hw',_⟩ := h.sel
  rw [eval_nonzero,h.width,ne_zero_iff,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show p.wx / 8 < 2 ^ 64 by omega)] at ht
  have := of_decide_eq_true (Option.some.inj ht)
  omega

theorem selected_ct : RelCT isa (Two VG.Proof.Bignum.AArch64.WindowFive.SelP)
    selected (fun _ _ => True) := by
  unfold selected VG.Impl.Rsa.AArch64.WindowSelectVector.select
  refine RelCT.seq (two_piece (Ψ := GuardCtx) [.x0]
    (pins_x0B (fun p : XPub => off p.B p.o) (fun _ _ ⟨_,_,_,_,hc,_⟩ => hc.good.x0))
    (by taint_decide) (fun _ _ h => guard_ready h)) ?_
  refine two_ite (Φ := GuardCtx) ?_ ?_ ?_
  · intro p s t hs ht
    rw [eval_nonzero,eval_nonzero,hs.width,ht.width]
  · refine two_ite ?_ ?_ ?_
    · intro p s t hs ht
      rw [eval_zero,eval_zero,hs.1.rem,ht.1.rem]
    · exact two_map id (fun _ _ h => ⟨h.1.1.sel,guard_width h.1.1 h.1.2⟩) blocked_ct
    · exact two_map id (fun _ _ h => h.1.1.sel) Selector.scalar.ct
  · exact two_map id (fun _ _ h => h.1.sel) Selector.scalar.ct

def selector : Selector := ⟨selected,selected_ok,selected_ct⟩

end VG.Proof.Bignum.AArch64.WindowVector
