module

public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedTrack
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCompare
import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowBase
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCst

/-! # Capturing a root and advancing the uninterrupted accumulator -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (aX aY aAcc aTmp sMask)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem capturePrefix_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma y : Nat} {v : Track} {j : Option Nat}
    (hc : Cst s B Z w minv N el E sigma) (hj : j = none ∨ j = some 1)
    (hv : TrackRep s.mem B w N v) (hy : y < N)
    (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % N)
    (he1 : word s.mem B (8 * sMask) = mask (decide (y * y % N = 1)))
    (hem : decide (s.gpr .rbp = 0) = decide (y * y % N = N - 1)) :
    WP isa (capturePrefix j) s fun u =>
      Cst u B Z w minv N el E sigma ∧
      TrackRep u.mem B w N (advance (permit j sigma) N y v) ∧
      wv u.mem B (slot w aY) w = y * 2 ^ (64 * w) % N ∧
      Frm B (rg w [aRoot] []) s.mem u.mem ∧ Keep mmRegs s u := by
  have hz := hc.hZ16
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have he2 := hc.e2
  have ht2 := hc.t2
  have hsigma : sigma < 2 ^ 64 := by omega
  have hfZ : flagsAt w + 16 ≤ 2 ^ 64 := by unfold flagsAt slot aRoot at *; omega
  unfold capturePrefix
  refine WP.seq (WP.mono (captureMasks_ok hc.ws hj hc.ht hsigma hem hv.active hv.found he1)
    fun s₁ ⟨h8, hsi, h12, hbp, m₁, k₁⟩ => ?_)
  have hflags := flags_write (m := s.mem) (B := B) hz
    (mask (!v.stopped && !(permit j sigma && (decide (y * y % N = 1) || decide (y * y % N = N - 1)))))
    (mask (v.found || (!v.stopped && permit j sigma && decide (y * y % N = 1))))
  dsimp only at hflags
  rw [← m₁] at hflags
  obtain ⟨f₁, root₁, active₁, found₁⟩ := hflags
  have hc₁ := hc.congr f₁ (by decide) (by simp) k₁ (by decide)
  have hy₁ : wv s₁.mem B (slot w aY) w = y * 2 ^ (64 * w) % N := by
    rw [f₁.rg_wv hz (by simp) (by decide) (by decide) (by omega), hY]
  have sr := hc₁.ws.sl (j := aRoot) (by decide)
  have sy := hc₁.ws.sl (j := aY) (by decide)
  refine WP.mono (sel_ok hc₁.ws.scr h8 hsi hbp h12 (by omega) (by omega)
    (by omega) (by omega) (by
      have := slot_far (w := w) (show aRoot ≠ aY by decide); omega)) fun s₂ ⟨root₂, out₂, k₂⟩ => ?_
  have f₂ : Frm B (rg w [aRoot] []) s₁.mem s₂.mem := Frm.rg_of_out out₂ (by omega) _ _ (by decide)
  have hc₂ := hc₁.congr f₂ (by decide) (by simp) k₂ (by decide)
  have r₂ : TrackRep s₂.mem B w N (advance (permit j sigma) N y v) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [root₂, root₁, hv.root, hy₁, advance_root]
      cases hh : (!v.stopped && permit j sigma && decide (y * y % N = 1)) <;> simp
    · rw [advance_root]
      split <;> first | exact hy | exact hv.rootlt
    · rw [out₂.word (Or.inr (by unfold flagsAt; omega)) (by omega), active₁, advance_active]
    · rw [out₂.word (Or.inr (by unfold flagsAt; omega)) (by omega), found₁, advance_found]
  refine ⟨hc₂, r₂, ?_, (f₁.rg_trans f₂).rg_mono (by decide) (by simp), (k₁.trans k₂).mono (by decide)⟩
  rw [f₂.rg_wv hz (by simp) (by decide) (by decide) (by omega)]; exact hy₁

theorem capture_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma y : Nat} {v : Track} {j : Option Nat}
    (hc : Cst s B Z w minv N el E sigma) (hj : j = none ∨ j = some 1)
    (hv : TrackRep s.mem B w N v) (hy : y < N)
    (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % N)
    (hX : wv s.mem B (slot w aX) w = y * y % N * 2 ^ (64 * w) % N)
    (he1 : word s.mem B (8 * sMask) = mask (decide (y * y % N = 1)))
    (hem : decide (s.gpr .rbp = 0) = decide (y * y % N = N - 1)) :
    WP isa (capture j) s fun u =>
      Cst u B Z w minv N el E sigma ∧
      TrackRep u.mem B w N (advance (permit j sigma) N y v) ∧
      wv u.mem B (slot w aY) w = y * y % N * 2 ^ (64 * w) % N ∧
      Frm B (rg w [aRoot, aY] []) s.mem u.mem ∧ Keep mmRegs s u := by
  have hz := hc.hZ16
  unfold capture
  refine WP.seq (WP.mono (capturePrefix_ok hc hj hv hy hY he1 hem)
    fun s₂ ⟨hc₂, r₂, _, f₂, k₂⟩ => ?_)
  refine WP.mono (RecoveryWindow.copy_ok hc₂ (o := aY) (a := aX)
    (by decide) (by decide) (by decide) (by decide)) fun u ⟨hcu, f₃, k₃, hy₃⟩ => ?_
  refine ⟨hcu, r₂.congr f₃ hz (by simp) (by decide), ?_, ?_, (k₂.trans k₃).mono (by decide)⟩
  · rw [hy₃, f₂.rg_wv hz (by simp) (by decide) (by decide) (by omega), hX]
  · exact (f₂.rg_trans f₃).rg_mono (by decide) (by simp)

end VG.Proof.Rsa.X86_64.RecoveryFolded
