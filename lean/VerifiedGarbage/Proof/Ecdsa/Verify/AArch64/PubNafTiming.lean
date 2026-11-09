module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WindowTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.PrepTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Points
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages

/-!
# Timing of verification with `[v]Q` by the public NAF

What the timing of `[v]Q` by the public NAF is stated about: one run's state
before the recoding of `v` (`NafWinState`), and two runs multiplying the same
point by the same scalar (`NafWinPublic`), with the fields they agree on
(`NafWinPublic.fields`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

variable {c : Cfg}

/-- One run's state before the recoding of `v`. -/
structure NafWinState (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s : State) : Prop where
  scr : Scr s base size
  fixed : ∃ g, Fixed c base g s.mem
  px : sv c base s PX < c.C.p
  py : sv c base s PY < c.C.p
  rep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
    (tmv c.C c.n base s (c.sl ONEP)) P
  scalar : sv c base s V = k

/-- Two runs multiplying the same point by the same scalar. -/
structure NafWinPublic (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s t : State) : Prop where
  left : NafWinState c base P k s
  right : NafWinState c base P k t
  sp : s.sp = t.sp
  px : tmv c.C c.n base s (c.sl PX) = tmv c.C c.n base t (c.sl PX)
  py : tmv c.C c.n base s (c.sl PY) = tmv c.C c.n base t (c.sl PY)

theorem NafWinPublic.fields {base : Addr} {P : Point c.C} {k : Nat} {s t : State}
    (h : NafWinPublic c base P k s t) :
    ∀ x ∈ winRo (winQ c), tmv c.C c.n base s x = tmv c.C c.n base t x := by
  obtain ⟨_, fs⟩ := h.left.fixed
  obtain ⟨_, ft⟩ := h.right.fixed
  intro x hx
  simp only [winRo, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · change toM _ _ (wordsVal s.mem base (c.sl AP) c.n) = toM _ _ (wordsVal t.mem base (c.sl AP) c.n)
    rw [fs.ap, ft.ap]
  · change toM _ _ (wordsVal s.mem base (c.sl BM) c.n) = toM _ _ (wordsVal t.mem base (c.sl BM) c.n)
    rw [fs.bm, ft.bm]
  · change toM _ _ (wordsVal s.mem base (c.sl ZERO) c.n) = toM _ _ (wordsVal t.mem base (c.sl ZERO) c.n)
    rw [fs.zero, ft.zero]
  · exact h.px
  · exact h.py
  · change toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n) = toM _ _ (wordsVal t.mem base (c.sl ONEP) c.n)
    rw [fs.onep, ft.onep]

end VG.Proof.Ecdsa.Verify.AArch64
