import VerifiedGarbage.Proof.Ecdh.AArch64.P192.Mul
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main

/-! # Peer multiplication followed by inversion -/

namespace VG.Proof.Ecdh.AArch64.P192

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdh.AArch64 VG.Impl.Ecdh.AArch64.P192
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P192
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

structure LadPost (base : Addr) (P : Point p192.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ powClob p192.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slW p192 gSlots ++ chainWc p192) s.mem s'.mem
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
    (hrx : sv p192 base s RX = 0) (hry : sv p192 base s RY = p192.mont 1) (hrz : sv p192 base s RZ = 0)
    (ht₀ : ∀ t < 64 * p192.n, s.mem (off base (bitsAt p192.n 0 + t)) = if (sv p192 base s K).testBit t then 1 else 0)
    {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', LadPost base P (sv p192 base s K) s s' → WP isa rest s' R) :
    WP isa (.seq qMul (.seq p192.pPow rest)) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * p192.n)
  refine WP.seq (WP.mono (qMul_ok hc hC hP hs F hpx hpy hrep (wordsVal_lt _ _ _ _) hrx hry hrz ht₀)
    fun s₃ ⟨K₃, U₃, M₃, L₃, R₃, _⟩ => ?_)
  have hs₃ := hs.of_keepRegs K₃ (x0_not_powClob h7)
  have rz₃ : wordsVal s₃.mem base (p192.sl RZ) p192.n < p192.C.p := L₃ _ (by simp)
  refine WP.seq (WP.mono (pPow_ok hc hs₃ M₃ rz₃)
    fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => h s₄ ?_)
  have r₄ : ∀ {i}, i < 45 → i ∉ [ACC, TMP] → sv p192 base s₄ i = sv p192 base s₃ i := fun hi h₁ =>
    sv_unch U₄ h7 hn hi (apart_chainWc hi h₁)
  refine ⟨hs₃.of_keepRegs K₄ (x0_not_powClob h7), fun r hr => ?_, by rw [K₄.rd, K₃.rd],
    by rw [K₄.wr, K₃.wr], U₃.trans U₄, ?_, lt₄, ?_, ?_⟩
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
