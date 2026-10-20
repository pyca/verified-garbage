module
public import VerifiedGarbage.Impl.Bignum.AArch64.FastFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul

import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSub
import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSel
import VerifiedGarbage.Proof.Bignum.Math

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FastFinish
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public
open VG.Proof.MlKem.AArch64 (Keep)

theorem finish_ok {s : State} {B : Addr} {Z w o : Nat}
    (hs : Scr s B Z) (hZ : slot w 8 ≤ Z)
    (h8 : s.gpr .x8 = off B (slot w aTmp)) (h10 : s.gpr .x10 = off B (slot w aN))
    (h6 : s.gpr .x6 = off B (slot w aAcc)) (h5 : s.gpr .x5 = off B (slot w o))
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h7 : s.gpr .x7 = 0)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hmod : w % 4 = 0) (ho : o < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (_hPos : 0 < wv s.mem B (slot w aN) w)
    (hTlt : wv s.mem B (slot w aTmp) (w+2) < 2*wv s.mem B (slot w aN) w) :
    WP isa VG.Impl.Bignum.AArch64.FastFinish.code s fun t =>
      wv t.mem B (slot w o) w = wv s.mem B (slot w aTmp) (w+2) % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have hwEq : 4*(w/4) = w := by omega
  unfold VG.Impl.Bignum.AArch64.FastFinish.code
  have sl : ∀ j < 8, slot w j+8*(w+2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sepAT : slot w aAcc+8*(w+2) = slot w aTmp := by unfold slot aAcc aTmp; omega
  have sepN : slot w aN+8*(w+2) ≤ slot w aAcc := by unfold slot aN aAcc; omega
  have soA := slot_sep (w := w) ho1
  have soT := slot_sep (w := w) ho2
  have hSub := sub_ok (n := w/4) hs h8 h10 h6 (by simpa only [hwEq] using h12) h7 (by omega) (by omega)
      (by have := sl aTmp (by decide); omega) (by have := sl aN (by decide); omega)
      (by have := sl aAcc (by decide); omega) (by omega) (by omega)
  simp only [hwEq] at hSub
  refine WP.seq (WP.mono hSub
    fun u ⟨c, hcu, hD, hou, ku⟩ => ?_)
  have u8 := (ku.gpr .x8 (by decide)).trans h8
  have u6 := (ku.gpr .x6 (by decide)).trans h6
  have u5 := (ku.gpr .x5 (by decide)).trans h5
  have u12 := (ku.gpr .x12 (by decide)).trans h12
  have hSel := sel_ok (n := w/4) (hs.congr ku.wr) u8 u6 u5
      (by simpa only [hwEq] using u12) hcu (by omega) (by omega)
      (by have := sl aTmp (by decide); omega) (by have := sl aAcc (by decide); omega)
      (by have := sl o ho; omega) (by omega) (by omega)
  simp only [hwEq] at hSel
  refine WP.mono hSel fun t ⟨hv, hot, kt⟩ => ?_
  have accU : wv u.mem B (slot w aTmp) w = wv s.mem B (slot w aTmp) w :=
    hou.wv (by omega) (by have := sl aTmp (by decide); omega)
  have hres : wv t.mem B (slot w o) w =
      wv s.mem B (slot w aTmp) (w+2) % wv s.mem B (slot w aN) w := by
    rw [hv, accU, wv_top2]
    have eq := csub_result (Tl := wv s.mem B (slot w aTmp) w)
      (Tw := (word s.mem B (slot w aTmp+8*w)).toNat)
      (Tw1 := (word s.mem B (slot w aTmp+8*w+8)).toNat)
      (D := wv u.mem B (slot w aAcc) w) (m := wv s.mem B (slot w aN) w)
      (R := 2 ^ (64*w)) (c := c.toNat)
      (by have := wv_lt s.mem B (slot w aN) w; omega) (wv_lt _ _ _ _)
      (Bool.toNat_le c) (wv_lt _ _ _ _) (by rw [← wv_top2]; exact hTlt) hD
    rw [← eq]
    by_cases h : (word s.mem B (slot w aTmp+8*w)).toNat < c.toNat <;> simp [h]
  refine ⟨hres, ?_, (ku.trans kt).mono (by decide)⟩
  have au : Arrays B w [aAcc, o] s.mem u.mem :=
    Arrays.of_outside (j := aAcc) (by simp) hou (Nat.le_refl _) (by omega)
  have aFinal : Arrays B w [aAcc, o] u.mem t.mem :=
    Arrays.of_outside (j := o) (by simp) hot (Nat.le_refl _) (by omega)
  exact au.trans aFinal

end VG.Proof.Bignum.AArch64.FastFinish
