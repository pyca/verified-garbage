module

public import VerifiedGarbage.Proof.Ecdh.AArch64.BrainpoolP384r1.Mul
import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages

/-! # Peer multiplication followed by inversion -/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.BrainpoolP384r1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdh.AArch64 VG.Impl.Ecdh.AArch64.BrainpoolP384r1
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP384r1
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

structure LadPost (base : Addr) (g : Reg → BitVec 64) (P : Point brainpoolp384r1.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ powClob brainpoolp384r1.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (qW ++ chainWc brainpoolp384r1) s.mem s'.mem
  fixed : Fixed brainpoolp384r1 base g s'.mem
  q : Rep brainpoolp384r1.C (tmv brainpoolp384r1.C brainpoolp384r1.n base s' (brainpoolp384r1.sl RX)) (tmv brainpoolp384r1.C brainpoolp384r1.n base s' (brainpoolp384r1.sl RY))
    (tmv brainpoolp384r1.C brainpoolp384r1.n base s' (brainpoolp384r1.sl RZ)) (mul k P)
  acc_lt : sv brainpoolp384r1 base s' ACC < brainpoolp384r1.C.p
  acc : toM brainpoolp384r1.C.p (2 ^ (64 * brainpoolp384r1.n)) (sv brainpoolp384r1 base s' ACC) = tmv brainpoolp384r1.C brainpoolp384r1.n base s' (brainpoolp384r1.sl RZ) ^ (brainpoolp384r1.C.p - 2)
  rz_lt : sv brainpoolp384r1 base s' RZ < brainpoolp384r1.C.p

/-- `[d]P` by windows, then `Z^(p-2)`. -/
theorem ladPow_ok (hc : BaseCfgOk brainpoolp384r1) (hC : Law brainpoolp384r1.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed brainpoolp384r1 base g s.mem) {P : Point brainpoolp384r1.C} (hP : onCurve brainpoolp384r1.C P = true)
    (hpx : sv brainpoolp384r1 base s PX < brainpoolp384r1.C.p) (hpy : sv brainpoolp384r1 base s PY < brainpoolp384r1.C.p)
    (hrep : Rep brainpoolp384r1.C (tmv brainpoolp384r1.C brainpoolp384r1.n base s (brainpoolp384r1.sl PX)) (tmv brainpoolp384r1.C brainpoolp384r1.n base s (brainpoolp384r1.sl PY))
      (tmv brainpoolp384r1.C brainpoolp384r1.n base s (brainpoolp384r1.sl ONEP)) P)
    {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', LadPost base g P (sv brainpoolp384r1 base s K) s s' → WP isa rest s' R) :
    WP isa (.seq qMul (.seq brainpoolp384r1.pPow rest)) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * brainpoolp384r1.n)
  refine WP.seq (WP.mono (qMul_ok hc hC hP hs F hpx hpy hrep)
    fun s₃ ⟨K₃, U₃, F₃, M₃, L₃, R₃, _⟩ => ?_)
  have hs₃ := hs.of_keepRegs K₃ (x0_not_powClob h7)
  have rz₃ : wordsVal s₃.mem base (brainpoolp384r1.sl RZ) brainpoolp384r1.n < brainpoolp384r1.C.p := L₃ _ (by simp)
  refine WP.seq (WP.mono (pPow_ok hc hs₃ M₃ rz₃)
    fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => h s₄ ?_)
  have r₄ : ∀ {i}, i < 45 → i ∉ [ACC, TMP] → sv brainpoolp384r1 base s₄ i = sv brainpoolp384r1 base s₃ i := fun hi h₁ =>
    sv_unch U₄ h7 hn hi (apart_chainWc hc hi h₁)
  refine ⟨hs₃.of_keepRegs K₄ (x0_not_powClob h7), fun r hr => ?_, by rw [K₄.rd, K₃.rd],
    by rw [K₄.wr, K₃.wr], U₃.trans U₄, F₃.unch h7 hn (fixedOk_chainWc hc) U₄, ?_, lt₄, ?_, ?_⟩
  · rw [K₄.gpr r hr, K₃.gpr r hr]
  · show Rep _ (toM _ _ (sv brainpoolp384r1 base s₄ RX)) (toM _ _ (sv brainpoolp384r1 base s₄ RY)) (toM _ _ (sv brainpoolp384r1 base s₄ RZ)) _
    rw [r₄ (i := RX) (by decide) (by decide), r₄ (i := RY) (by decide) (by decide),
      r₄ (i := RZ) (by decide) (by decide)]
    exact R₃
  · show _ = toM _ _ (sv brainpoolp384r1 base s₄ RZ) ^ _
    rw [r₄ (i := RZ) (by decide) (by decide)]
    exact v₄
  · rw [r₄ (i := RZ) (by decide) (by decide)]; exact rz₃

end VG.Proof.Ecdh.AArch64.BrainpoolP384r1
