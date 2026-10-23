module

public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTPieces
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT1
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTPieces
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCapture
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCompare
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedMasks
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCapture
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCompare
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedTrack
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedTrack

/-! # Constant-time uninterrupted squaring and masked root capture -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (aX aY aAcc aTmp sMask)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open Rp

/-- Secret values used only to justify bounds and preserve the workspace. -/
def SQ (stage : Nat) (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N E sigma y : Nat) (v : Track),
    Cst s p.B p.Z (wk p.k) minv N p.el E sigma ∧ TrackRep s.mem p.B (wk p.k) N v ∧ y < N ∧
    wv s.mem p.B (slot (wk p.k) aY) (wk p.k) = y * 2 ^ (64 * wk p.k) % N ∧
    (1 ≤ stage → wv s.mem p.B (slot (wk p.k) aX) (wk p.k) = y * y % N * 2 ^ (64 * wk p.k) % N) ∧
    (2 ≤ stage → word s.mem p.B (8 * sMask) = mask (decide (y * y % N = 1)) ∧
      decide (s.gpr .rbp = 0) = decide (y * y % N = N - 1))

theorem SQ.ws {stage : Nat} {p : RpP} {s : State} (h : SQ stage p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨_, _, _, _, _, _, hc, _⟩ := h
  exact hc.ws

/-- Squaring into X retains Y and the tracker. -/
theorem squareMul_ct (M : Mont) : RelCT isa (Two (SQ 0)) (M.mm aX aY aY) (Two (SQ 1)) := by
  refine mm_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) M (by unfold MmUse; decide)
    fun p s ⟨minv, N, E, sigma, y, v, hc, hv, hy, hY, _, _⟩ => ?_
  have hz := hc.hZ16
  have hN : 0 < N := by have := hc.n1; omega
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have hg := hc.good
  refine WP.mono (M.mm_ok hg.1 hg.2 hw1 (by omega) (o := aX) (a := aY) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
    (by rw [hc.hn, hY]; exact Nat.mod_lt _ hN)) fun u ⟨_, hlt, hmul, arr, k⟩ => ?_
  rw [hc.hn] at hlt hmul
  have hX := sq_mont hc.coprime hY hlt hmul
  have f : Frm p.B (rg (wk p.k) [aAcc, aTmp, aX] []) s.mem u.mem := Frm.rg_of_arrays arr _ _ (by decide)
  exact ⟨minv, N, E, sigma, y, v, hc.congr f (by decide) (by simp) k (by decide),
    hv.congr f hz (by simp) (by decide), hy,
    by rw [f.rg_wv hz (by simp) (by decide) (by decide) (by omega)]; exact hY,
    fun _ => hX, fun h => by omega⟩

theorem squareCompare_ct : RelCT isa (Two (SQ 1)) (comparisons aX) (Two (SQ 2)) := by
  refine comparisons_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (Or.inl rfl)
    fun p s ⟨minv, N, E, sigma, y, v, hc, hv, hy, hY, hX, _⟩ => ?_
  have hz := hc.hZ16
  have hN : 0 < N := by have := hc.n1; omega
  refine WP.mono (comparisons_ok hc (a := aX) (by decide) (Nat.mod_lt _ hN) (hX (by decide)))
    fun u ⟨hcu, he, hm, f, k⟩ => ?_
  exact ⟨minv, N, E, sigma, y, v, hcu, hv.congr f hz (by decide) (by simp), hy,
    by rw [f.rg_wv hz (by decide) (by decide) (by simp) (by omega)]; exact hY,
    fun _ => by rw [f.rg_wv hz (by decide) (by decide) (by simp) (by omega)]; exact hX (by decide),
    fun _ => ⟨he, decide_eq_decide.mpr hm⟩⟩

/-- The alignment shift selects a mask; both suffix squares execute. -/
theorem square_ct (M : Mont) (j : Option Nat) (hj : j = none ∨ j = some 1) :
    RelCT isa (Two (SQ 0)) (Folded.square M.mm j) fun _ _ => True := by
  simp only [Folded.square, seqs]
  refine RelCT.seq (squareMul_ct M) (RelCT.seq squareCompare_ct ?_)
  have ht : ∃ hint, (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.seq (.block (base aRoot .r8 ++ base aY .rsi ++ enabled j ++ captureCore)) (wordLoop 0 selBody)) hint).isSome = true := by
    rcases hj with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨hint, ht⟩ := ht
  apply (capture_gct (Ψ := fun _ _ => True) RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) j ht ?_ ?_).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  · intro p s ⟨minv, N, E, sigma, y, v, hc, hv, hy, hY, hX, hm⟩
    exact WP.mono (capturePrefix_ok hc hj hv hy hY (hm (by decide)).1 (hm (by decide)).2)
      fun _ ⟨hc', _⟩ => hc'.ws
  · intro p s ⟨minv, N, E, sigma, y, v, hc, hv, hy, hY, hX, hm⟩
    exact WP.mono (capture_ok hc hj hv hy hY (hX (by decide)) (hm (by decide)).1 (hm (by decide)).2) fun _ _ => trivial

end VG.Proof.Rsa.X86_64.RecoveryFolded
