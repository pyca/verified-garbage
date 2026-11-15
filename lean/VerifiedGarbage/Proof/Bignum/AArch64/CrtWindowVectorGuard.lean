module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStepCT
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStepCT
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

/-! Select SIMD only for complete public-width tiles, with a scalar fallback:
for a table of 16 or 32 entries (`select_ok`, `select_ct`), and RSA's of 32
with its scalar selector (`selector`). -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff eval_zero eq_zero_iff)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx Selector)
open VG.Impl.Rsa.AArch64.WindowSelectVector (select)

def guard : List Instr := [ldh .x12 sW, .lsr .x .x3 .x12 3, movi .x4 7,
  .logic .and .x .x4 .x12 .x4]

def selected : Prog isa := select 32 Selector.scalar.code

theorem shr3_width {w : Nat} (hw : w < 2 ^ 64) :
    BitVec.ofNat 64 w >>> 3 = BitVec.ofNat 64 (w / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show w / 8 < 2 ^ 64 by omega_using [hw])]

theorem guard_ok {s : State} {P : Addr} {w n : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx s P w mi X Xc n) (hw : w < 2 ^ 30) :
    WP isa (.block guard) s fun t =>
      (t.mem = s.mem ∧ t.gpr .x3 = BitVec.ofNat 64 (w / 8) ∧
        t.gpr .x4 = BitVec.ofNat 64 (w % 8)) ∧ Keep [.x12,.x3,.x4] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [guard, hc.good.x0, hdr_enc (show sW < 32 by decide), hc.ld (i := sW) (by decide),
    hc.good.hdr.hw, shr3_width (show w < 2 ^ 64 by omega_using [hw])]
  exact BlockedRedc.mask7_ofNat (by omega_using [hw])

/-- The selection from a table of `n` entries, 16 or 32: by vectors when the
width is whole tiles, and otherwise by `fallback`, which selects as it does. -/
theorem select_ok {s : State} {P : Addr} {w v n : Nat} {mi : BitVec 64} {X Xc : Nat} {fallback : Prog isa}
    (hN : n = 16 ∨ n = 32)
    (hf : ∀ {u : State}, CExpCtx u P w mi X Xc n → word u.mem P (8 * Crt.sTab) = off P (slot w 8) →
      word u.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v →
      WP isa fallback u fun t => CExpCtx t P w mi X Xc n ∧
        wv t.mem P (slot w Crt.aT) w = wv u.mem P (slot w (8 + v)) w ∧
        Frm P (selRanges w) u.mem t.mem ∧ Keep mmRegs u t)
    (hc : CExpCtx s P w mi X Xc n) (hw' : w < 2 ^ 30) (hv : v < n)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hNib : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (select n fallback) s fun t => CExpCtx t P w mi X Xc n ∧
      wv t.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w ∧
      Frm P (selRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold select
  refine WP.seq (WP.mono (guard_ok hc hw') fun u ⟨⟨hm,h3,h4⟩,ku⟩ => ?_)
  have ctx := hc.of_win (by rw [hm]; exact Frm.refl _ _ _) ku.wr (ku.gpr .x0 (by decide))
  have tab : word u.mem P (8 * Crt.sTab) = off P (slot w 8) := by rw [hm]; exact ht
  have nib : word u.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v := by rw [hm]; exact hNib
  have slow : WP isa fallback u (fun t => CExpCtx t P w mi X Xc n ∧
      wv t.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w ∧
      Frm P (selRanges w) s.mem t.mem ∧ Keep mmRegs s t) := WP.mono (hf ctx tab nib) fun t ⟨ct,hy,hf,kt⟩ =>
    ⟨ct,hm ▸ hy,hm ▸ hf,(ku.trans kt).mono (by decide)⟩
  by_cases fast : 8 ≤ w
  · refine WP.ite true (by rw [eval_nonzero,h3,ne_zero_iff,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show w / 8 < 2 ^ 64 by omega_using [hw']),decide_eq_true (show w / 8 ≠ 0 by omega_using [fast])])
      (fun _ => ?_) (by simp)
    by_cases hd : w % 8 = 0
    · refine WP.ite true (by rw [eval_zero,h4,hd]; rfl) (fun _ => ?_) (by simp)
      exact WP.mono (blockedN_ok hN ctx fast hw' hd hv tab nib) fun t ⟨ct,hy,hf,kt⟩ =>
        ⟨ct,hm ▸ hy,hm ▸ hf,(ku.trans kt).mono (by decide)⟩
    · exact WP.ite false (by rw [eval_zero,h4,eq_zero_iff,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show w % 8 < 2 ^ 64 by omega_using []),decide_eq_false hd]) (by simp) (fun _ => slow)
  · exact WP.ite false (by rw [eval_nonzero,h3,show w / 8 = 0 by omega_using [fast]]; rfl) (by simp) (fun _ => slow)

structure GuardCtx (n : Nat) (p : XPub) (s : State) : Prop where
  sel : SelPn n p s
  width : s.gpr .x3 = BitVec.ofNat 64 (p.wx / 8)
  rem : s.gpr .x4 = BitVec.ofNat 64 (p.wx % 8)

theorem guard_ready {n : Nat} {p : XPub} {s : State} (h : SelPn n p s) :
    WP isa (.block guard) s (GuardCtx n p) := by
  obtain ⟨mi,X,Xc,v,hc,hw,hw',hv,ht,hN⟩ := h
  refine WP.mono (guard_ok hc hw') fun u ⟨⟨hm,h3,h4⟩,ku⟩ => ?_
  exact ⟨⟨mi,X,Xc,v,hc.of_win (by rw [hm]; exact Frm.refl _ _ _) ku.wr
    (ku.gpr .x0 (by decide)),hw,hw',hv,hm ▸ ht,hm ▸ hN⟩,h3,h4⟩

theorem guard_width {n : Nat} {p : XPub} {s : State} (h : GuardCtx n p s)
    (ht : isa.eval (.nonzero .x .x3) s = some true) : 8 ≤ p.wx := by
  obtain ⟨_,_,_,_,_,_,hw',_⟩ := h.sel
  rw [eval_nonzero,h.width,ne_zero_iff,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show p.wx / 8 < 2 ^ 64 by omega_using [hw'])] at ht
  have := of_decide_eq_true (Option.some.inj ht)
  omega_using [this]

/-- The selection leaks the same in runs with the same workspace, as its
`fallback` does. -/
theorem select_ct {n : Nat} (hN : n = 16 ∨ n = 32) {fallback : Prog isa}
    (hf : RelCT isa (Two (SelPn n)) fallback (fun _ _ => True)) :
    RelCT isa (Two (SelPn n)) (select n fallback) (fun _ _ => True) := by
  unfold select
  refine RelCT.seq (two_piece (Ψ := GuardCtx n) [.x0]
    (pins_x0B (fun p : XPub => off p.B p.o) (fun _ _ ⟨_,_,_,_,hc,_⟩ => hc.good.x0))
    (by taint_decide) (fun _ _ h => guard_ready h)) ?_
  refine two_ite (Φ := GuardCtx n) ?_ ?_ ?_
  · intro p s t hs ht
    rw [eval_nonzero,eval_nonzero,hs.width,ht.width]
  · refine two_ite ?_ ?_ ?_
    · intro p s t hs ht
      rw [eval_zero,eval_zero,hs.1.rem,ht.1.rem]
    · exact two_map id (fun _ _ h => ⟨h.1.1.sel,guard_width h.1.1 h.1.2⟩) (blockedN_ct hN)
    · exact two_map id (fun _ _ h => h.1.1.sel) hf
  · exact two_map id (fun _ _ h => h.1.sel) hf

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

theorem selected_ct : RelCT isa (Two VG.Proof.Bignum.AArch64.WindowFive.SelP)
    selected (fun _ _ => True) :=
  two_map id (fun _ _ h => selP_n h)
    (select_ct (Or.inr rfl) (two_map id (fun _ _ h => selP_of_n h) Selector.scalar.ct))

def selector : Selector := ⟨selected,selected_ok,selected_ct⟩

end VG.Proof.Bignum.AArch64.WindowVector
