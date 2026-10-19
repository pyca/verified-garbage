module

public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math

/-! Canonical reduction reuses the existing subtraction and selection. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem finishBases_ok {s : State} {B : Addr} {Z w o : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (ho : o < 8) :
    WP isa (.block (VG.Impl.Bignum.AArch64.Square.finishBases o)) s fun t =>
      (t.gpr .x5 = off B (slot w o) ∧ t.gpr .x6 = off B (slot w aAcc) ∧ t.mem = s.mem) ∧
      Keep [.x5, .x6] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8*i)) 8 :=
    fun i hi => hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have so : sArr o < 32 := by unfold sArr; omega
  refine WP.keep [.x5, .x6] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.Square.finishBases
  brun [h0, hdr_enc so, hl _ so, hl _ (show sArr aAcc < 32 by decide),
    hH.harr o ho, hH.harr aAcc (by decide)]

theorem finish_ok {s : State} {B : Addr} {Z w o : Nat}
    (hs : Scr s B Z) (hZ : slot w 8 ≤ Z)
    (h8 : s.gpr .x8 = off B (slot w aTmp)) (h10 : s.gpr .x10 = off B (slot w aN))
    (h6 : s.gpr .x6 = off B (slot w aAcc)) (h5 : s.gpr .x5 = off B (slot w o))
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h7 : s.gpr .x7 = 0)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (ho : o < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (_hPos : 0 < wv s.mem B (slot w aN) w)
    (hTlt : wv s.mem B (slot w aTmp) (w+2) < 2*wv s.mem B (slot w aN) w) :
    WP isa (.seq subMod selectAcc) s fun t =>
      wv t.mem B (slot w o) w = wv s.mem B (slot w aTmp) (w+2) % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j+8*(w+2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sepAT : slot w aAcc+8*(w+2) = slot w aTmp := by unfold slot aAcc aTmp; omega
  have sepN : slot w aN+8*(w+2) ≤ slot w aAcc := by unfold slot aN aAcc; omega
  have soA := slot_sep (w := w) ho1
  have soT := slot_sep (w := w) ho2
  refine WP.seq (WP.mono (subMod_ok hs h8 h10 h6 h12 h7 hw hw'
    (by have := sl aTmp (by decide); omega) (by have := sl aN (by decide); omega)
    (by have := sl aAcc (by decide); omega) (by omega) (by omega))
    fun u ⟨c, hcu, hD, hou, ku⟩ => ?_)
  have u8 := (ku.gpr .x8 (by decide)).trans h8
  have u6 := (ku.gpr .x6 (by decide)).trans h6
  have u5 := (ku.gpr .x5 (by decide)).trans h5
  have u12 := (ku.gpr .x12 (by decide)).trans h12
  refine WP.mono (selectAcc_ok (hs.congr ku.wr) u8 u6 u5 u12 hcu hw hw'
    (by have := sl aTmp (by decide); omega) (by have := sl aAcc (by decide); omega)
    (by have := sl o ho; omega) (by omega) (by omega)) fun t ⟨hv, hot, kt⟩ => ?_
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

end VG.Proof.Bignum.AArch64.Square
