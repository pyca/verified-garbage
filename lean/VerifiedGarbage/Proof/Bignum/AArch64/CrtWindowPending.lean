module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailBit
import Mathlib.Data.Int.ModEq

/-! Tail-bit preparation preserves the Montgomery context and all source bytes. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (prepareBit)

theorem prepareBit_state {s : State} {P : Addr} {w b v V i : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hi : i < 8) (hv : v < 16) (hV : V < 256)
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v)
    (hb : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b)
    (hbyte : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) :
    WP isa (.block (prepareBit i)) s fun t => TableCtx t P w mi X Xc ∧
      wv t.mem P (slot w aY) w = wv s.mem P (slot w aY) w ∧
      word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 (2 * v + V / 2 ^ (7 - i) % 2) ∧
      word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (b + 1) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep [.x3,.x4,.x5] s t ∧
      (∀ k < 32, k ≠ Crt.sNib → k ≠ Crt.sBit →
        word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
      t.gpr .x3 = BitVec.ofNat 64 (b + 1) - BitVec.ofNat 64 5 := by
  refine WP.mono (prepareBit_ok hc hi hv hV hn hb hbyte) fun t ⟨⟨hm,hflag⟩,kt⟩ => ?_
  have oa := writeW_outside s.mem P (d := 8 * Crt.sNib) (BitVec.ofNat 64 (2 * v + V / 2 ^ (7 - i) % 2)) (by decide)
  have ob := writeW_outside (s.mem.writeW (off P (8 * Crt.sNib)) (BitVec.ofNat 64 (2 * v + V / 2 ^ (7 - i) % 2))) P
    (d := 8 * Crt.sBit) (BitVec.ofNat 64 (b + 1)) (by decide)
  rw [← hm] at ob
  have fa : Frm P (crtWinRanges w) _ _ := Frm.of_outside oa (by simp [crtWinRanges])
  have fb : Frm P (crtWinRanges w) _ _ := Frm.of_outside ob (by simp [crtWinRanges])
  have hf := fa.trans fb
  have hny : slot w aY + 8 * w ≤ 2 ^ 64 := by
    have := hc.good.scr.nowrap
    have := slot_le (w := w) (show aY < 8 by decide)
    omega
  refine ⟨hc.of_win hf kt.wr (kt.gpr .x0 (by decide)),?_,?_,?_,hf,kt,?_,hflag⟩
  · rw [ob.wv (by have := hdr_lt_slot w aY (show Crt.sBit < 32 by decide); omega) hny,
      oa.wv (by have := hdr_lt_slot w aY (show Crt.sNib < 32 by decide); omega) hny]
  · rw [hm,hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),word_writeW_self]
  · rw [hm,word_writeW_self]
  · intro k hk hn hb
    rw [hm,hdrStore_hdr _ _ _ (by decide) hk (Ne.symm hb),hdrStore_hdr _ _ _ (by decide) hk (Ne.symm hn)]


end VG.Proof.Bignum.AArch64.WindowFive
