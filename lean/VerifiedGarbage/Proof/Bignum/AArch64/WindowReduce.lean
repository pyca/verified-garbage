module

public import VerifiedGarbage.Impl.Bignum.AArch64.WindowArithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawTriangle
import VerifiedGarbage.Proof.Bignum.AArch64.WindowLazyBound
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.WindowLazyFinish
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowArithmetic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Reduction with a loose result, for the full radix-squared product range.
Only the window's final multiplication requires a canonical residue. -/
theorem lazy_ok {s : State} {B : Addr} {Z w o : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw : 16 ≤ w) (hw' : w < 2^31) (hmod : w % 8 = 0)
    (h8 : s.gpr .x8 = off B (slot w aAcc+16)) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (ho : o < 8) (_ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (hoN : o ≠ aN)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2^64 = 0) :
    WP isa (VG.Impl.Bignum.AArch64.WindowArithmetic.reduce o true) s fun t =>
      wv t.mem B (slot w o) w * 2^(64*w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w aAcc+16) (2*w) % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc,aTmp,o] s.mem t.mem ∧ Keep WindowRaw.regs s t := by
  have hn := hs.nowrap
  have hsep : slot w aN+8*(w+2) ≤ slot w aAcc+16 := by unfold slot aN aAcc; omega
  have hnz := slot_le (w := w) (show aN < 8 by decide)
  have htz := slot_le (w := w) (show aTmp < 8 by decide)
  have hoz := slot_le (w := w) ho
  have hso := slot_sep (w := w) ho2
  have hson := slot_sep (w := w) hoN
  unfold VG.Impl.Bignum.AArch64.WindowArithmetic.reduce
  simp only [ite_true]
  refine WP.seq (WP.mono (BlockedRedc.redc_layout_ok hs h0 hH hZ h8 h12 h7 hw
    (by omega) hmod) fun r ⟨hrValue,hrOut,hr8,hr10,hr12,hr7,kr⟩ => ?_)
  obtain ⟨q,hq,heq⟩ := hrValue hinv
  have hNR : wv r.mem B (slot w aN) w = wv s.mem B (slot w aN) w :=
    hrOut.wv (by omega) (by omega)
  have hHR := (Square.scratch_arrays hrOut).hdr hH
  have hlt : wv r.mem B (slot w aTmp) (w+2) < 2^(64*w)+wv s.mem B (slot w aN) w := by
    apply redc_lt_add hq _ heq
    simpa only [show 64*(2*w) = 64*w+64*w by omega, Nat.pow_add] using
      wv_lt s.mem B (slot w aAcc+16) (2*w)
  obtain ⟨bit,hbit,hval⟩ := WindowLazy.top_bit (wv_lt s.mem B (slot w aN) w) hlt
  refine WP.seq (WP.mono (Square.finishBases_ok (hs.congr kr.wr)
    ((kr.gpr .x0 (by decide)).trans h0) hHR hZ ho) fun c ⟨⟨hc5,hc6,hcm⟩,kc⟩ => ?_)
  have kw := kr.trans kc
  have hew : 4*(w/4) = w := by omega
  have hp := WindowLazy.finish_ok (bit := bit) (hs.congr kw.wr)
    ((kc.gpr .x8 (by decide)).trans hr8) ((kc.gpr .x10 (by decide)).trans hr10) hc5
    (by simpa only [hew] using (kc.gpr .x12 (by decide)).trans hr12)
    ((kc.gpr .x7 (by decide)).trans hr7) (by omega : 0 < w/4) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simpa only [hew,hcm] using hbit) (by simpa only [hew,hcm,hNR,← hval] using hlt)
  simp only [hew,hcm,← hval,hNR] at hp
  refine WP.mono hp fun t ⟨hv,ho',kt⟩ => ⟨?_,?_,(kw.trans kt).mono (by decide)⟩
  · rw [Nat.mul_mod, hv, ← Nat.mul_mod, Nat.mul_comm, heq, Nat.add_mul_mod_self_right]
  · have hFrame := (Square.scratch_arrays hrOut).mono (js' := [aAcc,aTmp,o]) (by simp)
    have ho'' : Outside B (slot w o) (8*w) r.mem t.mem := by simpa only [hcm] using ho'
    exact hFrame.trans (Arrays.of_outside (j := o) (by simp) ho'' (Nat.le_refl _) (by omega))

end VG.Proof.Bignum.AArch64.WindowArithmetic
