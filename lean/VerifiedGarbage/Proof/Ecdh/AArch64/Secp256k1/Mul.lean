module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.GMul
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst

/-! # secp256k1 multiplication of a point, by a call of `vg_secp256k1_mul` -/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.Secp256k1
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdh.AArch64.Secp256k1
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.Secp256k1

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
abbrev qW : List (Nat × Nat) := slW secp256k1 [EXPP] ++ gW

theorem qMul_ok (hc : BaseCfgOk secp256k1) (hC : Law secp256k1.C)
    {P : Point secp256k1.C} (hP : onCurve secp256k1.C P = true)
    {base : Addr} {g : Reg → BitVec 64} {s : State} (hs : Scr s base size)
    (F : Fixed secp256k1 base g s.mem)
    (hpx : sv secp256k1 base s PX < secp256k1.C.p) (hpy : sv secp256k1 base s PY < secp256k1.C.p)
    (hG : Rep secp256k1.C (tmv secp256k1.C 4 base s (secp256k1.sl PX))
      (tmv secp256k1.C 4 base s (secp256k1.sl PY)) (tmv secp256k1.C 4 base s (secp256k1.sl ONEP)) P) :
    WP isa qMul s fun s' => KeepRegs (powClob 4) s s' ∧
      Unch base qW s.mem s'.mem ∧ Fixed secp256k1 base g s'.mem ∧
      ModOkA secp256k1.MP' size secp256k1.C.p s'.mem base ∧
      (∀ x ∈ [secp256k1.sl RX, secp256k1.sl RY, secp256k1.sl RZ], wordsVal s'.mem base x 4 < secp256k1.C.p) ∧
      Rep secp256k1.C (tmv secp256k1.C 4 base s' (secp256k1.sl RX))
        (tmv secp256k1.C 4 base s' (secp256k1.sl RY))
        (tmv secp256k1.C 4 base s' (secp256k1.sl RZ)) (mul (sv secp256k1 base s K) P) ∧
      sv secp256k1 base s' EXPP = secp256k1.mont (3 * secp256k1.C.b) := by
  have hn := hs.nowrap
  have h7 := hc.n10
  have hp3 := hc.p_ge
  have hpR := unitMod_pow_two hc.p_odd (64 * secp256k1.n)
  refine WP.seq (WP.mono (setConst_ok hs (n := 4) (o := secp256k1.sl EXPP)
    (x := secp256k1.mont (3 * secp256k1.C.b)) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨b₁, K₁, O₁⟩ => ?_)
  have U₁ : Unch base (slW secp256k1 [EXPP]) s.mem s₁.mem := O₁.unch
  have hs₁ := hs.of_keepRegs K₁ (by decide)
  have F₁ := F.unch h7 hn (fixedOk_slW (l := [EXPP]) (by decide)) U₁
  have e₁ : ∀ {i}, i < 45 → i ≠ EXPP → sv secp256k1 base s₁ i = sv secp256k1 base s i :=
    fun hi he => sv_unch U₁ h7 hn hi (apart_slW (by simpa using he))
  have eP : ∀ {i}, i < 45 → i ≠ EXPP →
      tmv secp256k1.C 4 base s₁ (secp256k1.sl i) = tmv secp256k1.C 4 base s (secp256k1.sl i) :=
    fun hi he => congrArg (fun x => toM secp256k1.C.p (2 ^ (64 * secp256k1.n)) x) (e₁ hi he)
  have hone : tmv secp256k1.C 4 base s (secp256k1.sl ONEP) = 1 := by
    show toM _ _ (wordsVal s.mem base (secp256k1.sl ONEP) secp256k1.n) = 1
    rw [F.onep]; exact toM_one hpR
  rw [hone] at hG
  have hPe := affine_of_rep_one hC hG
  have hPe₁ : P = .affine (tmv secp256k1.C secp256k1.n base s₁ (secp256k1.sl PX)) (tmv secp256k1.C secp256k1.n base s₁ (secp256k1.sl PY)) := by
    show P = .affine (tmv secp256k1.C 4 base s₁ (secp256k1.sl PX)) (tmv secp256k1.C 4 base s₁ (secp256k1.sl PY))
    rw [eP (i := PX) (by decide) (by decide), eP (i := PY) (by decide) (by decide)]; exact hPe
  refine WP.mono (mulAt_ok hc (.inl rfl) (.inl (by decide)) ladLayM ladAM hC mulFn_v mulFn_nf
    (name := "vg_secp256k1_mul") (px := PX) (py := PY) (by decide) (by decide)
    (by decide) (by decide) (by decide) hs₁ F₁ (by rw [e₁ (by decide) (by decide)]; exact hpx)
    (by rw [e₁ (by decide) (by decide)]; exact hpy) (by rw [← hPe₁]; exact hP))
    fun s' ⟨K, U, F', M, L, R⟩ => ⟨(K₁.mono (by decide)).trans K, U₁.trans U, F', M, L, ?_, ?_⟩
  · rw [← hPe₁, e₁ (by decide) (by decide)] at R; exact R
  · exact (sv_unch U h7 hn (i := EXPP) (by decide)
      (apart_append (apart_slW (by decide)) (apart_mulWF (.inl (by decide)) (by decide) (by decide)))).trans b₁

end VG.Proof.Ecdh.AArch64.Secp256k1
