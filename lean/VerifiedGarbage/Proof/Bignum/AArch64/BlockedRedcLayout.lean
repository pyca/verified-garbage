module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcBody
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

theorem spill_arrays {s t : State} {B : Addr} {w o : Nat} (hw : 16 ≤ w)
    (ho : Outside B (slot w o) 88 s.mem t.mem) : Arrays B w [o] s.mem t.mem := by
  intro x hx
  have h := hx o (by simp)
  exact ho x (by omega)

theorem keep_restored {s t : State}
    (h : Keep (mmRegs ++ VG.Impl.Bignum.AArch64.BlockedRedc.saved) s t)
    (hs : ∀ r ∈ VG.Impl.Bignum.AArch64.BlockedRedc.saved, t.gpr r = s.gpr r) :
    Keep mmRegs s t := by
  refine ⟨?_, h.rd, h.wr, h.sp, h.vcs⟩
  intro r hr
  by_cases hsaved : r ∈ VG.Impl.Bignum.AArch64.BlockedRedc.saved
  · exact hs r hsaved
  · exact h.gpr r (by simp only [List.mem_append, not_or]; exact ⟨hr, hsaved⟩)

theorem redc_layout_ok {s : State} {B : Addr} {Z w : Nat} {minv : Word}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (h8 : s.gpr .x8 = off B (slot w aAcc + 16))
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h7 : s.gpr .x7 = 0)
    (hw16 : 16 ≤ w) (hw : w < 2 ^ 64) (hmod : w % 8 = 0) :
    WP isa VG.Impl.Bignum.AArch64.BlockedRedc.redc s fun t =>
      (((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 →
        ∃ q < 2 ^ (64 * w), 2 ^ (64 * w) * wv t.mem B (slot w aTmp) (w + 2) =
          wv s.mem B (slot w aAcc + 16) (2 * w) + q * wv s.mem B (slot w aN) w) ∧
      Outside B (slot w aAcc + 16) (8 * (2 * w + 2)) s.mem t.mem ∧
      t.gpr .x8 = off B (slot w aTmp) ∧ t.gpr .x10 = off B (slot w aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧ Keep rowRegs s t := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
  subst w
  have hEnd : slot (8 * k) aAcc + 16 + 64 * k = slot (8 * k) aTmp := by
    unfold slot aAcc aTmp; omega
  have hLimit := slot_le (w := 8 * k) (show aTmp < 8 by decide)
  refine WP.mono (redc_ok hs h0 h7 h8 h12
    (by unfold slot aAcc; omega) (by unfold slot aAcc aTmp at *; omega)
    (by unfold slot aAcc aN; omega) (by omega) (by omega)
    (hH.harr aN (by decide)) hH.hminv hH.hw)
    fun t ⟨hv, ho, ht8, ht10, ht12, ht7, kt⟩ => ?_
  rewrite [hEnd] at hv ht8
  have hCount : 2 * (8 * k) = 16 * k := by omega
  have hBytes : 8 * (2 * (8 * k) + 2) = 128 * k + 16 := by omega
  refine ⟨?_, ?_, ht8, ht10, ht12, ht7, kt⟩
  · rewrite [hCount]
    exact hv
  · rewrite [hBytes]
    exact ho

end VG.Proof.Bignum.AArch64.BlockedRedc
