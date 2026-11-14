module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.GMul
public import VerifiedGarbage.Impl.Ecdh.P192.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages

/-! ### `Ecdh.AArch64.P192.Mul`, which only this module used -/

section

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

end

end


/-! # Peer multiplication followed by inversion -/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P192

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdh.AArch64 VG.Impl.Ecdh.AArch64.P192
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P192
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

structure LadPost (base : Addr) (g : Reg → BitVec 64) (P : Point p192.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ powClob p192.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (qW ++ chainWc p192) s.mem s'.mem
  fixed : Fixed p192 base g s'.mem
  q : Rep p192.C (tmv p192.C p192.n base s' (p192.sl RX)) (tmv p192.C p192.n base s' (p192.sl RY))
    (tmv p192.C p192.n base s' (p192.sl RZ)) (mul k P)
  acc_lt : sv p192 base s' ACC < p192.C.p
  acc : toM p192.C.p (2 ^ (64 * p192.n)) (sv p192 base s' ACC) = tmv p192.C p192.n base s' (p192.sl RZ) ^ (p192.C.p - 2)
  rz_lt : sv p192 base s' RZ < p192.C.p

/-- `[d]P` by windows, then `Z^(p-2)`. -/
theorem ladPow_ok (hc : BaseCfgOk p192) (hC : Law p192.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed p192 base g s.mem) {P : Point p192.C} (hP : onCurve p192.C P = true)
    (hpx : sv p192 base s PX < p192.C.p) (hpy : sv p192 base s PY < p192.C.p)
    (hrep : Rep p192.C (tmv p192.C p192.n base s (p192.sl PX)) (tmv p192.C p192.n base s (p192.sl PY))
      (tmv p192.C p192.n base s (p192.sl ONEP)) P)
    {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', LadPost base g P (sv p192 base s K) s s' → WP isa rest s' R) :
    WP isa (.seq qMul (.seq p192.pPow rest)) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * p192.n)
  refine WP.seq (WP.mono (qMul_ok hc hC hP hs F hpx hpy hrep)
    fun s₃ ⟨K₃, U₃, F₃, M₃, L₃, R₃, _⟩ => ?_)
  have hs₃ := hs.of_keepRegs K₃ (x0_not_powClob h7)
  have rz₃ : wordsVal s₃.mem base (p192.sl RZ) p192.n < p192.C.p := L₃ _ (by simp)
  refine WP.seq (WP.mono (pPow_ok hc hs₃ M₃ rz₃)
    fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => h s₄ ?_)
  have r₄ : ∀ {i}, i < 45 → i ∉ [ACC, TMP] → sv p192 base s₄ i = sv p192 base s₃ i := fun hi h₁ =>
    sv_unch U₄ h7 hn hi (apart_chainWc hc hi h₁)
  refine ⟨hs₃.of_keepRegs K₄ (x0_not_powClob h7), fun r hr => ?_, by rw [K₄.rd, K₃.rd],
    by rw [K₄.wr, K₃.wr], U₃.trans U₄, F₃.unch h7 hn (fixedOk_chainWc hc) U₄, ?_, lt₄, ?_, ?_⟩
  · rw [K₄.gpr r hr, K₃.gpr r hr]
  · show Rep _ (toM _ _ (sv p192 base s₄ RX)) (toM _ _ (sv p192 base s₄ RY)) (toM _ _ (sv p192 base s₄ RZ)) _
    rw [r₄ (i := RX) (by decide) (by decide), r₄ (i := RY) (by decide) (by decide),
      r₄ (i := RZ) (by decide) (by decide)]
    exact R₃
  · show _ = toM _ _ (sv p192 base s₄ RZ) ^ _
    rw [r₄ (i := RZ) (by decide) (by decide)]
    exact v₄
  · rw [r₄ (i := RZ) (by decide) (by decide)]; exact rz₃

end VG.Proof.Ecdh.AArch64.P192
