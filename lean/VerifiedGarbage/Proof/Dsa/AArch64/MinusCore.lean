module

public import VerifiedGarbage.Proof.Dsa.AArch64.MinusHead
public import VerifiedGarbage.Proof.Dsa.AArch64.MinusStep

/-! # Exact subtraction of a small public value from the modulus -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem minusCore_ok {s : State} {B : Addr} {Z w amount : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (ha : amount < 2 ^ 16) (hm : amount ≤ wv s.mem B (slot w aN) w) :
    WP isa (.seq (.block (minusHead amount)) (countLoop .x14 minusTail)) s fun t =>
      wv t.mem B (slot w aY) w = wv s.mem B (slot w aN) w - amount ∧
      Outside B (slot w aY) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hz := hg.scr.nowrap
  have hy := Nat.le_trans (slot_le (w := w) (show aY < 8 by decide)) hZ
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hsep := slot_sep (w := w) (show aY ≠ aN by decide)
  refine WP.seq (WP.mono (minusHead_ok hg hZ (by omega) hw' ha)
    fun u ⟨hu14, hu16, hu17, hu7, hfu, hv, hku⟩ => ?_)
  have huN : ∀ k ≤ w, wv u.mem B (slot w aN) k = wv s.mem B (slot w aN) k :=
    fun k hk => hfu.wv (by omega) (by omega)
  have h0 : MinusInv u B Z (slot w aN) (slot w aY) amount (0 + 1) u :=
    ⟨hg.scr.congr hku.wr, Keep.refl _ _, by simpa using hu16, by simpa using hu17,
      Outside.refl _ _ _ _, by rw [huN 1 (by omega)]; exact hv⟩
  refine WP.mono (wp_countdown (N := w - 1) (by omega) (by omega)
    (fun j t => MinusInv u B Z (slot w aN) (slot w aY) amount (j + 1) t)
    (fun j hj t hi _ => minusStep_ok hu7 (by omega) (by omega) (by omega) (by omega) hi) h0 hu14)
    fun t ht => ?_
  have he : w - 1 + 1 = w := by omega
  rw [he] at ht
  have hv := ht.val
  rw [huN w (Nat.le_refl _)] at hv
  have hvlt := wv_lt t.mem B (slot w aY) w
  refine ⟨?_, (hfu.mono (Nat.le_refl _) (by omega)).trans ht.out, (hku.trans ht.keep).mono (by decide)⟩
  cases hc : t.c <;> simp only [hc, Bool.not_false, Bool.not_true, Bool.toNat_false, Bool.toNat_true,
    Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hv <;> omega

end VG.Proof.Dsa.AArch64
