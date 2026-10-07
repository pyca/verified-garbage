import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused

/-! The final conditional subtraction, shared with the ADX multiplier. -/

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- Reduce the result below `2 m` by the existing constant-time subtraction
and selection. -/
theorem finish_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z)
    (hw1 : 2 ≤ w) (hw : w < 2 ^ 31) (h10 : s.gpr .r10 = off B (slot w aN))
    {o : Nat} (ho : o < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (hTlt : wv s.mem B (slot w aTmp) (w + 2) < 2 * wv s.mem B (slot w aN) w) :
    WP isa (Adx.finish o) s fun t =>
      wv t.mem B (slot w o) w = wv s.mem B (slot w aTmp) (w + 2) % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega
  have hTs := sl aTmp (by decide)
  have sNX : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega
  have soX : slot w o + 8 * (w + 2) ≤ slot w aAcc ∨ slot w aTmp + 8 * (w + 2) ≤ slot w o := by
    have := slot_sep (w := w) ho1; have := slot_sep (w := w) ho2; unfold slot aAcc aTmp at *; omega
  unfold Adx.finish
  refine WP.seq (WP.mono (finishBases_ok hs hdi hH hZ ho) fun s₁ ⟨h12, h8, hsi, hbx, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (subMod_ok (hs.congr k₁.2.2) h8 ((k₁.gpr (by decide)).trans h10) hsi h12 (by omega) hw
    (by omega) (by have := sl aN (by decide); omega) (by omega) (by omega) (by omega))
    fun s₂ ⟨c, lt, hbp, hlt, hD, ho₂, k₂⟩ => ?_)
  rw [hm₁] at hlt hD ho₂
  have k12 := k₁.trans k₂
  refine WP.mono (selectAcc_ok (hs.congr k12.2.2) ((k₂.gpr (by decide)).trans h8) ((k₂.gpr (by decide)).trans hsi)
    ((k₂.gpr (by decide)).trans hbx) ((k₂.gpr (by decide)).trans h12) hbp (by omega) hw (by omega) (by omega)
    (by have := sl o ho; omega) (by omega) (by omega)) fun t ⟨hv, hot, kt⟩ => ?_
  have hT₂ : wv s₂.mem B (slot w aTmp) w = wv s.mem B (slot w aTmp) w := ho₂.wv (by omega) (by omega)
  refine ⟨?_, ?_, (k12.trans kt).mono (by decide)⟩
  · rw [hv, hT₂, hlt, wv_top2]
    have h := VG.Proof.Bignum.csub_result (Tl := wv s.mem B (slot w aTmp) w)
      (Tw := (word s.mem B (slot w aTmp + 8 * w)).toNat)
      (Tw1 := (word s.mem B (slot w aTmp + 8 * w + 8)).toNat) (D := wv s₂.mem B (slot w aAcc) w)
      (m := wv s.mem B (slot w aN) w) (R := 2 ^ (64 * w)) (c := c.toNat)
      (by have := wv_lt s.mem B (slot w aN) w; omega) (wv_lt _ _ _ _) (Bool.toNat_le c) (wv_lt _ _ _ _)
      (by rw [← wv_top2]; exact hTlt) hD
    rw [← h]
    by_cases h : (word s.mem B (slot w aTmp + 8 * w)).toNat < c.toNat <;> simp [h]
  · intro x hx
    have h1 := hx aAcc (by simp)
    have h2 := hx o (by simp)
    exact (hot x (by omega)).trans (ho₂ x (by omega))

end VG.Proof.Bignum.X86_64.AdxSquare
