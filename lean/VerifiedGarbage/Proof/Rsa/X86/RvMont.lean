module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Rsa.X86.RvMontGeometry

import VerifiedGarbage.Proof.Rsa.X86.RvMontSetup
import VerifiedGarbage.Proof.Rsa.X86.RvMontInverse
import VerifiedGarbage.Proof.Rsa.X86.RvMontPower
import VerifiedGarbage.Proof.Rsa.X86.RvSubtract
import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Rsa.X86.RvOps

/-! # The prime-recovery Montgomery setup stage -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

def AM (A : Nat → Nat) (n m : Nat) : Nat → Nat :=
  upd (upd (upd (upd (upd (upd (upd A aZ 0) aOne 1) mBase m)
    mR2 (2 ^ (128 * n) % m)) mXm (2 ^ (64 * n) % m)) aO (2 ^ (64 * n) % m))
    aNg (m - 2 ^ (64 * n) % m)

theorem upd_twice (A : Nat → Nat) (j x y : Nat) : upd (upd A j x) j y = upd A j y := by
  funext i
  simp only [upd]
  split <;> rfl

abbrev liveM : List Nat := [aNg, aO, mR2, mBase, aOne, aZ, aN]

theorem mont_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m : Nat}
    (h : KS g s0 A [aN] AW [wR] V [sTc, sCnt] s)
    (value : A aN = m) (bound : m < 2 ^ (64 * g.n))
    (odd : m % 2 = 1) (hm : 1 < m) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.mont s fun t =>
      KS g s0 (AM A g.n m) liveM AW [wR] V [sTc, sCnt] t ∧ MR g m t := by
  have value32 : A 32 = m := value
  unfold VG.Impl.Rsa.X86.RecoverRt.mont
  simp only [seqs]
  refine WP.seq (WP.mono (h.sub_w (o := aZ) (a := aN) (b := aN)
    (by decide) (by simp) (by simp) (by decide) (by decide) (by omega)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s1 ⟨h1, _⟩ => ?_)
  simp only [Nat.sub_self] at h1
  refine WP.seq (WP.mono (h1.copy_w (o := aOne) (a := aZ) (by decide) (by simp) (by decide)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s2 ⟨h2, _, _⟩ => ?_)
  simp only [upd_self] at h2
  refine WP.seq (WP.mono (h2.setOne_w (j := aOne) (by simp)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s3 ⟨h3, _⟩ => ?_)
  simp only [upd_self, Nat.zero_div, Nat.mul_zero, Nat.add_zero, upd_twice] at h3
  refine WP.seq (WP.mono (h3.copy_w (o := mBase) (a := aN) (by decide) (by simp) (by decide)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s4 ⟨h4, _, _⟩ => ?_)
  have vn : upd (upd A aZ 0) aOne 1 aN = m := by simpa only [upd, show aN ≠ aOne by decide, show aN ≠ aZ by decide, ite_false] using value
  rw [vn] at h4
  refine WP.seq (WP.mono (h4.setupInverse (by simp) (by simp [upd]) bound odd
    (by decide)) fun s5 ⟨h5, mr5⟩ => ?_)
  refine WP.seq (WP.mono (h5.setupR2 mr5 hm (by simp) (by simp [upd, aN, aZ, aOne, mBase, value32]) (by simp)
    (by simp [upd, aZ, aOne, mBase]) (by simp) (by simp [upd, aOne, mBase]) (by decide) (by decide) (by decide)) fun s6 ⟨h6, mr6⟩ => ?_)
  refine WP.seq (WP.mono (h6.copyMont mr6 (o := mXm) (a := aOne) (by decide)
    (by simp) (by decide) (by decide) (by decide)) fun s7 ⟨h7, mr7, _⟩ => ?_)
  have vone : upd (upd (upd (upd A aZ 0) aOne 1) mBase m)
      mR2 (2 ^ (128 * g.n) % m) aOne = 1 := by simp [upd, aOne, mBase, mR2]
  rw [vone] at h7
  refine WP.seq (WP.mono (h7.mmul mr7 (o := mXm) (a := mXm) (b := mR2)
    (by decide) (by decide) (by decide) (by decide) (by simp) (by simp)
    (by simpa [upd] using hm)
    (by simpa [upd, mXm, mR2] using Nat.mod_lt (2 ^ (128 * g.n)) (by omega : 0 < m))
    (by decide) (by decide)) fun s8 ⟨X, h8, mr8, _, xlt, xe⟩ => ?_)
  have vx : X = 2 ^ (64 * g.n) % m := mont_one odd xlt (by simpa [upd, mXm, mR2] using xe)
  rw [vx] at h8
  simp only [upd_twice] at h8
  refine WP.seq (WP.mono (h8.copyMont mr8 (o := aO) (a := mXm) (by decide)
    (by simp) (by decide) (by decide) (by decide)) fun s9 ⟨h9, mr9, _⟩ => ?_)
  simp only [upd_self] at h9
  refine WP.mono (h9.subMont mr9 (o := aNg) (a := aN) (b := aO)
    (by decide) (by decide) (by simp) (by simp)
    (by simpa [upd, aN, aZ, aOne, mBase, mR2, mXm, aO, value32] using
      Nat.le_of_lt (Nat.mod_lt (2 ^ (64 * g.n)) (by omega : 0 < m)))
    (by decide)) fun t ⟨ht, mt⟩ => ?_
  refine ⟨ht.mono ?_ (by simp) (by simp), mt⟩
  intro j hj
  simp only [liveM, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [AM, upd, aNg, aO, mXm, mR2, mBase, aOne, aZ, aN, value32]

end VG.Proof.Rsa.X86.Recover
