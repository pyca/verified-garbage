module

public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCst
public import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Rsa.X86_64.RpSq
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.RecoverMath

/-! # Comparing a folded accumulator with Montgomery ±1 -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (sMask)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem comparisons_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma a x : Nat} (hc : Cst s B Z w minv N el E sigma)
    (ha : a < 16) (hx : x < N) (hv : wv s.mem B (slot w a) w = x * 2 ^ (64 * w) % N) :
    WP isa (comparisons a) s fun u =>
      Cst u B Z w minv N el E sigma ∧
      word u.mem B (8 * sMask) = mask (decide (x = 1)) ∧
      (u.gpr .rbp = 0 ↔ x = N - 1) ∧
      Frm B (rg w [] [sMask]) s.mem u.mem ∧ Keep mmRegs s u := by
  have hZ16 := hc.hZ16
  have hR := hc.coprime
  have hN1 : 1 < N := by have := hc.n1; omega
  unfold comparisons
  rw [show eqA a aO ++ [.block (eqStore sMask)] ++ eqA a aNg =
      eqA a aO ++ ([.block (eqStore sMask)] ++ eqA a aNg) by rw [List.append_assoc]]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok hc.ws ha (by decide))
    fun s₁ ⟨hz₁, m₁, k₁⟩ => ?_)
  rw [hv, hc.ho, eq_one_mont hR hN1 hx rfl] at hz₁
  have hc₁ := hc.congr (js := []) (hs := []) (by rw [m₁]; exact Frm.refl _ _ _)
    (by simp) (by simp) k₁ (by decide)
  refine WP.seq (WP.mono (eqStore_ok hc₁.ws (i := sMask) (by decide) (by decide))
    fun s₂ ⟨m₂, k₂⟩ => ?_)
  have he : decide (s₁.gpr .rbp = 0) = decide (x = 1) := decide_eq_decide.mpr hz₁
  rw [he] at m₂
  have hf₂ : Frm B (rg w [] [sMask]) s₁.mem s₂.mem := by
    rw [m₂]
    exact Frm.rg_of_hdr (writeW_outside _ _ _ (by decide)) [] [sMask] (by decide)
  have hc₂ := hc₁.congr hf₂ (by decide) (by decide) k₂ (by decide)
  have hv₂ : wv s₂.mem B (slot w a) w = x * 2 ^ (64 * w) % N := by
    rw [hf₂.rg_wv hZ16 (by decide) ha (by simp) (by omega), m₁, hv]
  refine WP.mono (eqA_ok hc₂.ws ha (by decide)) fun u ⟨hz₃, m₃, k₃⟩ => ?_
  rw [hv₂, hc₂.hng, eq_neg_mont hR hN1 hx rfl] at hz₃
  have hc₃ := hc₂.congr (js := []) (hs := []) (by rw [m₃]; exact Frm.refl _ _ _)
    (by simp) (by simp) k₃ (by decide)
  refine ⟨hc₃, ?_, hz₃, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [m₃, m₂, word_writeW_self]
  · rw [m₃]
    rw [m₁] at hf₂
    exact hf₂

end VG.Proof.Rsa.X86_64.RecoveryFolded
