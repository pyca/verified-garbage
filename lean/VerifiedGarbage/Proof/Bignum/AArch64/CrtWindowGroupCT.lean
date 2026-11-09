module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCoreCT

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowDigit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore

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
    oa.wv (by have := hdr_lt_slot p.wx aY (show Crt.sNib < 32 by decide); omega)
      (by have := hc.good.scr.nowrap
          have := slot_le (w := p.wx) (show aY < 8 by decide); omega)
  exact ⟨mi, X, Xc, V / 2 ^ shift % 32,
    hc.of_win fa ka.wr (ka.gpr .x0 (by decide)), ht.of_win fa hc.scrT.nowrap,
    ya.symm ▸ hy, hw, hw', hR, Nat.mod_lt _ (by decide), by rw [hm, word_writeW_self]⟩

end VG.Proof.Bignum.AArch64.WindowFive
