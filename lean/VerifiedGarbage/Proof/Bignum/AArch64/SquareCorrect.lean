module
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul

import VerifiedGarbage.Proof.Bignum.AArch64.SquareRaw
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedc
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega

/-! Squaring preserves the existing Montgomery contract, including allowed aliases. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem redc_lt {R T X q m : Nat} (hm : 0 < m) (hq : q < R)
    (hX : X < m*R) (he : R*T = X+q*m) : T < 2*m := by
  have hqm : q*m < R*m := Nat.mul_lt_mul_of_pos_right hq hm
  have hb : R*T < R*(2*m) := by
    rw [he]
    have h1 : m*R = R*m := Nat.mul_comm _ _
    have h2 : R*(2*m) = R*m+R*m := by grind
    omega
  exact Nat.lt_of_mul_lt_mul_left hb

theorem square_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31)
    {o a : Nat} (ho : o < 8) (ha : a < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat*minv.toNat+1) % 2 ^ 64 = 0)
    (hA : wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w) :
    WP isa (VG.Impl.Bignum.AArch64.Square.square o a) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w*2 ^ (64*w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w*wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have hNs := slot_le (w := w) (show aN < 8 by decide)
  have hsep : slot w aN+8*(w+2) ≤ slot w aAcc := by unfold slot aN aAcc; omega
  have hmpos : 0 < wv s.mem B (slot w aN) w := by omega
  unfold VG.Impl.Bignum.AArch64.Square.square
  refine WP.seq (WP.mono (rawSquare_ok hs h0 hH hZ hw1 (by omega) ha ha1 ha2)
    fun u ⟨_, hv1, ho1', h8, h10, h12, h15, h7, _, ku⟩ => ?_)
  have hN0 : word u.mem B (slot w aN) = word s.mem B (slot w aN) := ho1'.word (by omega) (by omega)
  have hN1 : wv u.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho1'.wv (by omega) (by omega)
  refine WP.seq (WP.mono (redc_ok (hs.congr ku.wr) hZ h8 h10 h12 h15 h7 hw1 (by omega))
    fun v ⟨hv2, ho2', v8, v10, v12, v7, kv⟩ => ?_)
  have invu : ((word u.mem B (slot w aN)).toNat*minv.toNat+1) % 2 ^ 64 = 0 := by rw [hN0]; exact hinv
  obtain ⟨q, hq, heq⟩ := hv2 invu
  rw [hv1, hN1] at heq
  have ho12 := ho1'.trans ho2'
  have hN2 : wv v.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho12.wv (by omega) (by omega)
  have k12 := ku.trans kv
  have hH2 := (scratch_arrays ho12).hdr hH
  have hTlt : wv v.mem B (slot w aTmp) (w+2) < 2*wv s.mem B (slot w aN) w :=
    redc_lt hmpos hq (Nat.mul_lt_mul'' hA (wv_lt _ _ _ _)) heq
  refine WP.seq (WP.mono (finishBases_ok (hs.congr k12.wr)
    ((k12.gpr .x0 (by decide)).trans h0) hH2 hZ ho)
    fun c ⟨⟨c5, c6, hmc⟩, kc⟩ => ?_)
  have kAll := k12.trans kc
  refine WP.mono (finish_ok (hs.congr kAll.wr) hZ
    ((kc.gpr .x8 (by decide)).trans v8) ((kc.gpr .x10 (by decide)).trans v10) c6 c5
    ((kc.gpr .x12 (by decide)).trans v12) ((kc.gpr .x7 (by decide)).trans v7)
    (by omega) hw ho ho1 ho2 (by rw [hmc, hN2]; exact hmpos)
    (by rw [hmc, hN2]; exact hTlt)) fun t ⟨hres, hframe, kt⟩ => ?_
  rw [hmc, hN2] at hres
  refine ⟨?_, ?_, ?_, (kAll.trans kt).mono (by decide)⟩
  · rw [hres]; exact Nat.mod_lt _ hmpos
  · rw [hres, Nat.mod_mul_mod, Nat.mul_comm, heq, Nat.add_mul_mod_self_right]
  · have a12 : Arrays B w [aAcc, aTmp, o] s.mem v.mem :=
      (scratch_arrays ho12).mono (by
        intro j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl <;> simp)
    have aft := hframe.mono (js' := [aAcc, aTmp, o]) (by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
      rcases hj with rfl | rfl <;> simp)
    rw [hmc] at aft
    exact a12.trans aft

end VG.Proof.Bignum.AArch64.Square
