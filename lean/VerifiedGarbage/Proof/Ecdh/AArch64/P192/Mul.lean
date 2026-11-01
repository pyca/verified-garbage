module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.GMul
public import VerifiedGarbage.Impl.Ecdh.P192.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst

/-! # p192 multiplication of a point, by a call of `vg_p192_mul` -/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P192

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.P192
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdh.AArch64.P192
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P192

/-- A point that coordinates with `Z = 1` stand for is the affine point of
their `X` and `Y`. -/
theorem affine_of_rep_one {C : Curve} (hC : Law C) {X Y : Fe C} {P : Point C} (h : Rep C X Y 1 P) :
    P = .affine X Y := by
  cases P with
  | infinity => exact absurd h.2.2 hC.one_ne_zero
  | affine x y =>
    obtain ⟨-, hx, hy⟩ := h
    rw [Lean.Grind.Semiring.mul_one] at hx hy
    rw [hx, hy]

/-- What `qMul` writes: the call's, and `EXPP`'s slot. -/
abbrev qW : List (Nat × Nat) := slW p192 [EXPP] ++ gW

theorem qMul_ok (hc : BaseCfgOk p192) (hC : Law p192.C)
    {P : Point p192.C} (hP : onCurve p192.C P = true)
    {base : Addr} {g : Reg → BitVec 64} {s : State} (hs : Scr s base size)
    (F : Fixed p192 base g s.mem)
    (hpx : sv p192 base s PX < p192.C.p) (hpy : sv p192 base s PY < p192.C.p)
    (hG : Rep p192.C (tmv p192.C 4 base s (p192.sl PX))
      (tmv p192.C 4 base s (p192.sl PY)) (tmv p192.C 4 base s (p192.sl ONEP)) P) :
    WP isa qMul s fun s' => KeepRegs (powClob 4) s s' ∧
      Unch base qW s.mem s'.mem ∧ Fixed p192 base g s'.mem ∧
      ModOkA p192.MP' size p192.C.p s'.mem base ∧
      (∀ x ∈ [p192.sl RX, p192.sl RY, p192.sl RZ], wordsVal s'.mem base x 4 < p192.C.p) ∧
      Rep p192.C (tmv p192.C 4 base s' (p192.sl RX))
        (tmv p192.C 4 base s' (p192.sl RY))
        (tmv p192.C 4 base s' (p192.sl RZ)) (mul (sv p192 base s K) P) ∧
      sv p192 base s' EXPP = p192.mont (3 * p192.C.b) := by
  have hn := hs.nowrap
  have h7 := hc.n10
  have hp3 := hc.p_ge
  have hpR := unitMod_pow_two hc.p_odd (64 * p192.n)
  refine WP.seq (WP.mono (setConst_ok hs (n := 4) (o := p192.sl EXPP)
    (x := p192.mont (3 * p192.C.b)) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨b₁, K₁, O₁⟩ => ?_)
  have U₁ : Unch base (slW p192 [EXPP]) s.mem s₁.mem := O₁.unch
  have hs₁ := hs.of_keepRegs K₁ (by decide)
  have F₁ := F.unch h7 hn (fixedOk_slW (l := [EXPP]) (by decide)) U₁
  have e₁ : ∀ {i}, i < 45 → i ≠ EXPP → sv p192 base s₁ i = sv p192 base s i :=
    fun hi he => sv_unch U₁ h7 hn hi (apart_slW (by simpa using he))
  have eP : ∀ {i}, i < 45 → i ≠ EXPP →
      tmv p192.C 4 base s₁ (p192.sl i) = tmv p192.C 4 base s (p192.sl i) :=
    fun hi he => congrArg (fun x => toM p192.C.p (2 ^ (64 * p192.n)) x) (e₁ hi he)
  have hone : tmv p192.C 4 base s (p192.sl ONEP) = 1 := by
    show toM _ _ (wordsVal s.mem base (p192.sl ONEP) p192.n) = 1
    rw [F.onep]; exact toM_one hpR
  rw [hone] at hG
  have hPe := affine_of_rep_one hC hG
  have hPe₁ : P = .affine (tmv p192.C p192.n base s₁ (p192.sl PX)) (tmv p192.C p192.n base s₁ (p192.sl PY)) := by
    show P = .affine (tmv p192.C 4 base s₁ (p192.sl PX)) (tmv p192.C 4 base s₁ (p192.sl PY))
    rw [eP (i := PX) (by decide) (by decide), eP (i := PY) (by decide) (by decide)]; exact hPe
  refine WP.mono (mulAt_ok hc (.inl rfl) (.inl (by decide)) ladLayM ladAM hC mulFn_v mulFn_nf
    (name := "vg_p192_mul") (px := PX) (py := PY) (by decide) (by decide)
    (by decide) (by decide) (by decide) hs₁ F₁ (by rw [e₁ (by decide) (by decide)]; exact hpx)
    (by rw [e₁ (by decide) (by decide)]; exact hpy) (by rw [← hPe₁]; exact hP))
    fun s' ⟨K, U, F', M, L, R⟩ => ⟨(K₁.mono (by decide)).trans K, U₁.trans U, F', M, L, ?_, ?_⟩
  · rw [← hPe₁, e₁ (by decide) (by decide)] at R; exact R
  · exact (sv_unch U h7 hn (i := EXPP) (by decide)
      (apart_append (apart_slW (by decide)) (apart_mulWF (.inl (by decide)) (by decide) (by decide)))).trans b₁

end VG.Proof.Ecdh.AArch64.P192
