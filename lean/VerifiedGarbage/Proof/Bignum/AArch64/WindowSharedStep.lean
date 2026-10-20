module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowShared
import VerifiedGarbage.Proof.Bignum.AArch64.WindowOperations
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawTriangle
import VerifiedGarbage.Proof.Bignum.CrtWindowRelation
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
import Mathlib.Data.Int.ModEq

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

theorem square_ok {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : 16 ≤ w) (hw' : w < 2^30) (hmod : w % 8 = 0) :
    WP isa (VG.Impl.Bignum.AArch64.WindowArithmetic.square 6) s fun t =>
      TableCtx t P w mi X Xc ∧
      wv t.mem P (slot w aY) w * 2^(64*w) % X =
        wv s.mem P (slot w aY) w * wv s.mem P (slot w aY) w % X ∧
      (∀ k < 32, word t.mem P (8*k) = word s.mem P (8*k)) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep WindowRaw.regs s t := by
  refine WP.mono (WindowArithmetic.square_ok hc.good.scr hc.good.x0 hc.good.hdr
    (Nat.le_refl _) hw (by omega) hmod (by decide) (by decide) (by decide) (by decide) hc.inv)
    fun t ⟨ht,ha,kt⟩ => ?_
  rw [hc.n] at ht
  have hf : Frm P (crtWinRanges w) s.mem t.mem := Frm.of_arrays ha (by simp [crtWinRanges, aY])
  exact ⟨hc.of_win hf kt.wr (kt.gpr .x0 (by decide)),ht,fun k hk => ha.hslot hk,hf,kt⟩

theorem decrement_ok {s : State} {P : Addr} {w j : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hj : j < 5)
    (hb : word s.mem P (8*Crt.sBit) = BitVec.ofNat 64 (5-j)) :
    WP isa (.block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]) s fun t =>
      (t.mem = s.mem.writeW (off P (8*Crt.sBit)) (BitVec.ofNat 64 (5-(j+1))) ∧
        t.gpr .x3 = BitVec.ofNat 64 (5-(j+1))) ∧ Keep [.x3] s t := by
  simpa only [show 5-j-1 = 5-(j+1) by omega] using
    WindowFive.crtBitEnd_ok hc hb (by omega)

theorem step_ok {s : State} {P : Addr} {w j A k : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : 16 ≤ w) (hw' : w < 2^30) (hmod : w % 8 = 0)
    (hj : j < 5) (hb : word s.mem P (8*Crt.sBit) = BitVec.ofNat 64 (5-j))
    (hv : wv s.mem P (slot w aY) w * (2^(64*w))^k % X = A % X) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.step s fun t =>
      TableCtx t P w mi X Xc ∧
      wv t.mem P (slot w aY) w * (2^(64*w))^(2*k+1) % X = A^2 % X ∧
      word t.mem P (8*Crt.sBit) = BitVec.ofNat 64 (5-(j+1)) ∧
      t.gpr .x3 = BitVec.ofNat 64 (5-(j+1)) ∧
      (∀ i < 32, i ≠ Crt.sBit → word t.mem P (8*i) = word s.mem P (8*i)) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep WindowRaw.regs s t := by
  unfold VG.Impl.Rsa.AArch64.WindowShared.step
  refine WP.seq (WP.mono (square_ok hc hw hw' hmod) fun u ⟨cu,hu,hhu,fu,ku⟩ => ?_)
  refine WP.mono (decrement_ok cu hj (by rw [hhu _ (by decide)]; exact hb))
    fun t ⟨⟨hm,h3⟩,kt⟩ => ?_
  have hwrite := writeW_outside u.mem P (d := 8*Crt.sBit) (BitVec.ofNat 64 (5-(j+1))) (by decide)
  rw [← hm] at hwrite
  have ft : Frm P (crtWinRanges w) u.mem t.mem := Frm.of_outside hwrite (by simp [crtWinRanges])
  have hy : wv t.mem P (slot w aY) w = wv u.mem P (slot w aY) w := by
    apply hwrite.wv
    · have := hdr_lt_slot w aY (show Crt.sBit < 32 by decide); omega
    · have := slot_le (w := w) (show aY < 8 by decide); have := cu.good.scr.nowrap; omega
  refine ⟨cu.of_win ft kt.wr (kt.gpr .x0 (by decide)),?_,?_,h3,?_,fu.trans ft,(ku.trans kt).mono (by decide)⟩
  · rw [hy]; exact CrtWindowFive.square_scale hu hv
  · rw [hm,word_writeW_self]
  · intro i hi hb'
    rw [hm,hdrStore_hdr _ _ _ (by decide) hi (Ne.symm hb'),hhu i hi]

end VG.Proof.Bignum.AArch64.WindowShared
