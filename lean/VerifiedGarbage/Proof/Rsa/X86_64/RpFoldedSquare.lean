module

import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCapture
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCompare
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCst
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedTrack

/-! # One square of the uninterrupted exponentiation accumulator -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (aX aY aAcc aTmp sMask)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem square_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma y : Nat} {v : Track} {j : Option Nat}
    (hc : Cst s B Z w minv N el E sigma) (hj : j = none ∨ j = some 1)
    (hv : TrackRep s.mem B w N v) (hy : y < N)
    (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % N) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.Recover.Folded.square M.mm j) s fun u =>
      Cst u B Z w minv N el E sigma ∧
      TrackRep u.mem B w N (advance (permit j sigma) N y v) ∧
      wv u.mem B (slot w aY) w = y * y % N * 2 ^ (64 * w) % N ∧
      Frm B (rg w [aAcc, aTmp, aX, aRoot, aY] [sMask]) s.mem u.mem ∧ Keep mmRegs s u := by
  have hz := hc.hZ16
  have hR := hc.coprime
  have hN1 : 0 < N := by have := hc.n1; omega
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have hYlt : wv s.mem B (slot w aY) w < N := by rw [hY]; exact Nat.mod_lt _ hN1
  have hg := hc.good
  simp only [VG.Impl.Rsa.X86_64.Keys.Recover.Folded.square, seqs]
  refine WP.seq (WP.mono (M.mm_ok hg.1 hg.2 hw1 (by omega) (o := aX) (a := aY) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
    (by rw [hc.hn]; exact hYlt)) fun s₁ ⟨_, hlt₁, hmul₁, arr₁, k₁⟩ => ?_)
  rw [hc.hn] at hlt₁ hmul₁
  have hX₁ := sq_mont hR hY hlt₁ hmul₁
  have f₁ : Frm B (rg w [aAcc, aTmp, aX] []) s.mem s₁.mem := Frm.rg_of_arrays arr₁ _ _ (by decide)
  have hc₁ := hc.congr f₁ (by decide) (by simp) k₁ (by decide)
  refine WP.seq (WP.mono (comparisons_ok hc₁ (a := aX) (by decide) (Nat.mod_lt _ hN1) hX₁)
    fun s₂ ⟨hc₂, he1₂, hem₂, f₂, k₂⟩ => ?_)
  have ht₂ := (hv.congr f₁ hz (by simp) (by decide)).congr f₂ hz (by decide) (by simp)
  have hy₂ : wv s₂.mem B (slot w aY) w = y * 2 ^ (64 * w) % N := by
    rw [f₂.rg_wv hz (by decide) (by decide) (by simp) (by omega),
      f₁.rg_wv hz (by simp) (by decide) (by decide) (by omega), hY]
  have hx₂ : wv s₂.mem B (slot w aX) w = y * y % N * 2 ^ (64 * w) % N := by
    rw [f₂.rg_wv hz (by decide) (by decide) (by simp) (by omega), hX₁]
  refine WP.mono (capture_ok hc₂ hj ht₂ hy hy₂ hx₂ he1₂ (decide_eq_decide.mpr hem₂))
    fun u ⟨hcu, htu, hyu, f₃, k₃⟩ => ?_
  exact ⟨hcu, htu, hyu, ((f₁.rg_trans f₂).rg_trans f₃).rg_mono (by decide) (by decide),
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

end VG.Proof.Rsa.X86_64.RecoveryFolded
