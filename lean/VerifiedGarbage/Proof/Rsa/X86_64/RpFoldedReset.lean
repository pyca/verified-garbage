module

import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedResetMasks
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCompare
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedTrack
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverFolded
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.Rsa.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCst

/-! # The root tracker after the multiplication by a window's power -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (aY sMask)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

def resetTrack (d N y : Nat) (v : Track) : Track :=
  if d = 0 then v else VG.Proof.Rsa.RecoveryFolded.start N y v.root

theorem reset_root (d N y : Nat) (v : Track) : (resetTrack d N y v).root = v.root := by
  unfold resetTrack
  split <;> rfl

theorem reset_active (d N y : Nat) (v : Track) :
    (!(resetTrack d N y v).stopped) =
      (if d = 0 then !v.stopped else !(decide (y = 1) || decide (y = N - 1))) := by
  unfold resetTrack
  split <;> rfl

theorem reset_found (d N y : Nat) (v : Track) :
    (resetTrack d N y v).found = (v.found && decide (d = 0)) := by
  by_cases hd : d = 0
  · simp [resetTrack, hd]
  · simp [resetTrack, hd, VG.Proof.Rsa.RecoveryFolded.start]

theorem digit_zero (V : BitVec 64) :
    decide ((V >>> 62) = 0) = decide (V.toNat / 2 ^ 62 = 0) := by
  have hn : (V >>> 62).toNat = V.toNat / 2 ^ 62 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  apply decide_eq_decide.mpr
  constructor
  · intro he
    have hh := congrArg BitVec.toNat he
    rw [hn] at hh
    exact hh
  · intro he
    apply BitVec.eq_of_toNat_eq
    rw [hn, he]
    rfl

theorem reset_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma y : Nat} {v : Track} {V : BitVec 64}
    (hc : Cst s B Z w minv N el E sigma) (hv : TrackRep s.mem B w N v) (hy : y < N)
    (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % N)
    (hV : word s.mem B (8 * sC2) = V) :
    WP isa reset s fun u =>
      Cst u B Z w minv N el E sigma ∧
      TrackRep u.mem B w N (resetTrack (V.toNat / 2 ^ 62) N y v) ∧
      Frm B (rg w [aRoot] [sMask]) s.mem u.mem ∧ Keep mmRegs s u := by
  have hz := hc.hZ16
  unfold reset
  refine WP.seq (WP.mono (comparisons_ok hc (a := aY) (by decide) hy hY)
    fun s₁ ⟨hc₁, he₁, hm₁, f₁, k₁⟩ => ?_)
  have r₁ := hv.congr f₁ hz (by decide) (by simp)
  have hV₁ : word s₁.mem B (8 * sC2) = V := by
    rw [f₁.rg_word (by decide) (by decide)]; exact hV
  refine WP.mono (resetMasks_ok (d0 := decide (V.toNat / 2 ^ 62 = 0)) (alive := !v.stopped)
    (ok := v.found) (e1 := decide (y = 1)) (em := decide (y = N - 1)) (V := V) hc₁.ws
    (decide_eq_decide.mpr hm₁) r₁.active r₁.found he₁ hV₁ (digit_zero V)) fun u ⟨mu, ku⟩ => ?_
  have hflags := flags_write (m := s₁.mem) (B := B) hz
    (mask (if decide (V.toNat / 2 ^ 62 = 0) then !v.stopped else !(decide (y = 1) || decide (y = N - 1))))
    (mask (v.found && decide (V.toNat / 2 ^ 62 = 0)))
  dsimp only at hflags
  rw [← mu] at hflags
  obtain ⟨f₂, root₂, active₂, found₂⟩ := hflags
  have hcu := hc₁.congr f₂ (by decide) (by simp) ku (by decide)
  refine ⟨hcu, ?_, (f₁.rg_trans f₂).rg_mono (by decide) (by decide), (k₁.trans ku).mono (by decide)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [root₂, r₁.root, reset_root]
  · rw [reset_root]; exact r₁.rootlt
  · rw [active₂, reset_active]
    simp only [decide_eq_true_eq]
  · rw [found₂, reset_found]

end VG.Proof.Rsa.X86_64.RecoveryFolded
