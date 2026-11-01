module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.GMul
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst

/-! # brainpoolP384r1 multiplication of a point, by a call of `vg_brainpoolp384r1_mul` -/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.BrainpoolP384r1

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.BrainpoolP384r1
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdh.AArch64.BrainpoolP384r1
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP384r1

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
abbrev qW : List (Nat × Nat) := slW brainpoolp384r1 [EXPP] ++ gW

theorem qMul_ok (hc : BaseCfgOk brainpoolp384r1) (hC : Law brainpoolp384r1.C)
    {P : Point brainpoolp384r1.C} (hP : onCurve brainpoolp384r1.C P = true)
    {base : Addr} {g : Reg → BitVec 64} {s : State} (hs : Scr s base size)
    (F : Fixed brainpoolp384r1 base g s.mem)
    (hpx : sv brainpoolp384r1 base s PX < brainpoolp384r1.C.p) (hpy : sv brainpoolp384r1 base s PY < brainpoolp384r1.C.p)
    (hG : Rep brainpoolp384r1.C (tmv brainpoolp384r1.C brainpoolp384r1.n base s (brainpoolp384r1.sl PX))
      (tmv brainpoolp384r1.C brainpoolp384r1.n base s (brainpoolp384r1.sl PY)) (tmv brainpoolp384r1.C brainpoolp384r1.n base s (brainpoolp384r1.sl ONEP)) P) :
    WP isa qMul s fun s' => KeepRegs (powClob 6) s s' ∧
      Unch base qW s.mem s'.mem ∧ Fixed brainpoolp384r1 base g s'.mem ∧
      ModOkA brainpoolp384r1.MP' size brainpoolp384r1.C.p s'.mem base ∧
      (∀ x ∈ [brainpoolp384r1.sl RX, brainpoolp384r1.sl RY, brainpoolp384r1.sl RZ], wordsVal s'.mem base x brainpoolp384r1.n < brainpoolp384r1.C.p) ∧
      Rep brainpoolp384r1.C (tmv brainpoolp384r1.C brainpoolp384r1.n base s' (brainpoolp384r1.sl RX))
        (tmv brainpoolp384r1.C brainpoolp384r1.n base s' (brainpoolp384r1.sl RY))
        (tmv brainpoolp384r1.C brainpoolp384r1.n base s' (brainpoolp384r1.sl RZ)) (mul (sv brainpoolp384r1 base s K) P) ∧
      sv brainpoolp384r1 base s' EXPP = brainpoolp384r1.mont (3 * brainpoolp384r1.C.b) := by
  have hn := hs.nowrap
  have h7 := hc.n10
  have hp3 := hc.p_ge
  have hpR := unitMod_pow_two hc.p_odd (64 * brainpoolp384r1.n)
  refine WP.seq (WP.mono (setConst_ok hs (n := 6) (o := brainpoolp384r1.sl EXPP)
    (x := brainpoolp384r1.mont (3 * brainpoolp384r1.C.b)) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨b₁, K₁, O₁⟩ => ?_)
  have U₁ : Unch base (slW brainpoolp384r1 [EXPP]) s.mem s₁.mem := O₁.unch
  have hs₁ := hs.of_keepRegs K₁ (by decide)
  have F₁ := F.unch h7 hn (fixedOk_slW (l := [EXPP]) (by decide)) U₁
  have e₁ : ∀ {i}, i < 45 → i ≠ EXPP → sv brainpoolp384r1 base s₁ i = sv brainpoolp384r1 base s i :=
    fun hi he => sv_unch U₁ h7 hn hi (apart_slW (by simpa using he))
  have eP : ∀ {i}, i < 45 → i ≠ EXPP →
      tmv brainpoolp384r1.C brainpoolp384r1.n base s₁ (brainpoolp384r1.sl i) = tmv brainpoolp384r1.C brainpoolp384r1.n base s (brainpoolp384r1.sl i) :=
    fun hi he => congrArg (fun x => toM brainpoolp384r1.C.p (2 ^ (64 * brainpoolp384r1.n)) x) (e₁ hi he)
  have hone : tmv brainpoolp384r1.C brainpoolp384r1.n base s (brainpoolp384r1.sl ONEP) = 1 := by
    show toM _ _ (wordsVal s.mem base (brainpoolp384r1.sl ONEP) brainpoolp384r1.n) = 1
    rw [F.onep]; exact toM_one (m := brainpoolp384r1.C.p) (R := 2 ^ (64 * brainpoolp384r1.n)) hpR
  rw [hone] at hG
  have hPe := affine_of_rep_one hC hG
  have hPe₁ : P = .affine (tmv brainpoolp384r1.C brainpoolp384r1.n base s₁ (brainpoolp384r1.sl PX)) (tmv brainpoolp384r1.C brainpoolp384r1.n base s₁ (brainpoolp384r1.sl PY)) := by
    show P = .affine (tmv brainpoolp384r1.C brainpoolp384r1.n base s₁ (brainpoolp384r1.sl PX)) (tmv brainpoolp384r1.C brainpoolp384r1.n base s₁ (brainpoolp384r1.sl PY))
    rw [eP (i := PX) (by decide) (by decide), eP (i := PY) (by decide) (by decide)]; exact hPe
  refine WP.mono (mulAt_ok hc (.inr (.inl rfl)) (.inr (by decide)) ladLayM ladAM hC mulFn_v mulFn_nf
    (name := "vg_brainpoolp384r1_mul") (px := PX) (py := PY) (by decide) (by decide)
    (by decide) (by decide) (by decide) hs₁ F₁ (by rw [e₁ (by decide) (by decide)]; exact hpx)
    (by rw [e₁ (by decide) (by decide)]; exact hpy) (by rw [← hPe₁]; exact hP))
    fun s' ⟨K, U, F', M, L, R⟩ => ⟨(K₁.mono (by decide)).trans K, U₁.trans U, F', M, L, ?_, ?_⟩
  · rw [← hPe₁, e₁ (by decide) (by decide)] at R; exact R
  · exact (sv_unch U h7 hn (i := EXPP) (by decide)
      (apart_append (apart_slW (by decide)) (apart_mulWF (.inr (by decide)) (by decide) (by decide)))).trans b₁

end VG.Proof.Ecdh.AArch64.BrainpoolP384r1
