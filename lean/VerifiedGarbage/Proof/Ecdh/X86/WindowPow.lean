import VerifiedGarbage.Proof.Ecdsa.X86.Inv
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Ecdh.X86.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowMul

/-! # Signed-window multiplication followed by affine conversion for x86 ECDH -/
namespace VG.Proof.Ecdh.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdsa.Verify.X86
open VG.Impl.Ecdh.X86 (PX PY)
variable {c : Cfg}

abbrev ecWindowW (c : Cfg) : List (Nat × Nat) := windowW c ++ pwW c

structure WindowPost (c : Cfg) (base : Addr) (k : Nat) (P : Point c.C) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ powClob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (ecWindowW c) s.mem s'.mem
  q : Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
    (tmv c.C c.n base s' (c.sl RZ)) (mul k P)
  acc_lt : sv c base s' ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = tmv c.C c.n base s' (c.sl RZ) ^ (c.C.p - 2)
  rz_lt : sv c base s' RZ < c.C.p

theorem windowPow_ok (hc : CfgOk c) (h4 : c.n = 4) (hC : Law c.C) (ham3 : AM3 c.C)
    {base : Addr} {s : State} (hs : Scr s base size) {g : Reg → BitVec 32}
    (F : Fixed c base g s.mem) {P : Point c.C} (hP : onCurve c.C P = true)
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hQ : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    (ht₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0)
    {rest : Prog isa} {R : State → Prop} (h : ∀ s', WindowPost c base (sv c base s K) P s s' → WP isa rest s' R) :
    WP isa (.seq (Impl.Ecdh.X86.Cfg.windowMul c (c.sl K)) (.seq c.pPow rest)) s R := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono (windowMulAt_ok hc h4 (i := K) (by decide) (by decide)
    hC ham3 hs F hP hpx hpy hQ) fun s₅ ⟨K₅, U₅, M₅, L₅, R₅⟩ => ?_)
  have hs₅ := hs.of_keeps K₅ (by decide)
  have F₅ := F.unch h7 hn (windowW_fixed h4) U₅
  have rz₅ : wordsVal s₅.mem base (c.sl RZ) c.n < c.C.p :=
    L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine WP.seq (WP.mono (pPow_ok hc hs₅ M₅ rz₅
    F₅.onep (fun t ht => by
      change  t < 64 * c.n at ht
      change s₅.mem (off base (bitsAt c.n 1 + t)) = _
      rw [U₅.byte (windowW_table h4 ht) (by rw [bitsAt_eq, h4]; rw [h4] at ht; omega)]
      exact ht₁ t ht)
    (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega)) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  have r₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₆ i = sv c base s₅ i := fun hi h₁ =>
    sv_unch U₆ h7 hn hi (apart_pwW hi h₁)
  refine ⟨hs₅.of_keeps K₆ (by decide), fun r hr => by rw [K₆.1 r hr, K₅.1 r hr],
    by rw [K₆.2.1, K₅.2.1], by rw [K₆.2.2, K₅.2.2], U₅.trans U₆, ?_, lt₆, ?_, ?_⟩
  · change Rep c.C (toM _ _ (sv c base s₆ RX)) (toM _ _ (sv c base s₆ RY))
      (toM _ _ (sv c base s₆ RZ)) _
    rw [r₆ (i := RX) (by decide) (by decide), r₆ (i := RY) (by decide) (by decide),
      r₆ (i := RZ) (by decide) (by decide)]
    exact R₅
  · change _ = toM _ _ (sv c base s₆ RZ) ^ _
    rw [r₆ (i := RZ) (by decide) (by decide)]
    exact v₆
  · rw [r₆ (i := RZ) (by decide) (by decide)]; exact rz₅

end VG.Proof.Ecdh.X86
