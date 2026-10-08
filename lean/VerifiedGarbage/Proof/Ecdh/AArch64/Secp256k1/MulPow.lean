import VerifiedGarbage.Proof.Ecdh.AArch64.Secp256k1.Mul
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main

/-! # Peer multiplication followed by inversion -/

namespace VG.Proof.Ecdh.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdh.AArch64 VG.Impl.Ecdh.AArch64.Secp256k1
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.Secp256k1
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

structure LadPost (base : Addr) (P : Point secp256k1.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ powClob secp256k1.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slW secp256k1 gSlots ++ chainWc secp256k1) s.mem s'.mem
  q : Rep secp256k1.C (tmv secp256k1.C secp256k1.n base s' (secp256k1.sl RX)) (tmv secp256k1.C secp256k1.n base s' (secp256k1.sl RY))
    (tmv secp256k1.C secp256k1.n base s' (secp256k1.sl RZ)) (mul k P)
  acc_lt : sv secp256k1 base s' ACC < secp256k1.C.p
  acc : toM secp256k1.C.p (2 ^ (64 * secp256k1.n)) (sv secp256k1 base s' ACC) = tmv secp256k1.C secp256k1.n base s' (secp256k1.sl RZ) ^ (secp256k1.C.p - 2)
  rz_lt : sv secp256k1 base s' RZ < secp256k1.C.p

/-- `[d]P` by windows, then `Z^(p-2)`. -/
theorem ladPow_ok (hc : BaseCfgOk secp256k1) (hC : Law secp256k1.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed secp256k1 base g s.mem) {P : Point secp256k1.C} (hP : onCurve secp256k1.C P = true)
    (hpx : sv secp256k1 base s PX < secp256k1.C.p) (hpy : sv secp256k1 base s PY < secp256k1.C.p)
    (hrep : Rep secp256k1.C (tmv secp256k1.C secp256k1.n base s (secp256k1.sl PX)) (tmv secp256k1.C secp256k1.n base s (secp256k1.sl PY))
      (tmv secp256k1.C secp256k1.n base s (secp256k1.sl ONEP)) P)
    (hrx : sv secp256k1 base s RX = 0) (hry : sv secp256k1 base s RY = secp256k1.mont 1) (hrz : sv secp256k1 base s RZ = 0)
    (ht₀ : ∀ t < 64 * secp256k1.n, s.mem (off base (bitsAt secp256k1.n 0 + t)) = if (sv secp256k1 base s K).testBit t then 1 else 0)
    {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', LadPost base P (sv secp256k1 base s K) s s' → WP isa rest s' R) :
    WP isa (.seq qMul (.seq secp256k1.pPow rest)) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * secp256k1.n)
  refine WP.seq (WP.mono (qMul_ok hc hC hP hs F hpx hpy hrep (wordsVal_lt _ _ _ _) hrx hry hrz ht₀)
    fun s₃ ⟨K₃, U₃, M₃, L₃, R₃, _⟩ => ?_)
  have hs₃ := hs.of_keepRegs K₃ (x0_not_powClob h7)
  have rz₃ : wordsVal s₃.mem base (secp256k1.sl RZ) secp256k1.n < secp256k1.C.p := L₃ _ (by simp)
  refine WP.seq (WP.mono (pPow_ok hc hs₃ M₃ rz₃)
    fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => h s₄ ?_)
  have r₄ : ∀ {i}, i < 45 → i ∉ [ACC, TMP] → sv secp256k1 base s₄ i = sv secp256k1 base s₃ i := fun hi h₁ =>
    sv_unch U₄ h7 hn hi (apart_chainWc hi h₁)
  refine ⟨hs₃.of_keepRegs K₄ (x0_not_powClob h7), fun r hr => ?_, by rw [K₄.rd, K₃.rd],
    by rw [K₄.wr, K₃.wr], U₃.trans U₄, ?_, lt₄, ?_, ?_⟩
  · rw [K₄.gpr r hr, K₃.gpr r hr]
  · show Rep _ (toM _ _ (sv secp256k1 base s₄ RX)) (toM _ _ (sv secp256k1 base s₄ RY)) (toM _ _ (sv secp256k1 base s₄ RZ)) _
    rw [r₄ (i := RX) (by decide) (by decide), r₄ (i := RY) (by decide) (by decide),
      r₄ (i := RZ) (by decide) (by decide)]
    exact R₃
  · show _ = toM _ _ (sv secp256k1 base s₄ RZ) ^ _
    rw [r₄ (i := RZ) (by decide) (by decide)]
    exact v₄
  · rw [r₄ (i := RZ) (by decide) (by decide)]; exact rz₃

end VG.Proof.Ecdh.AArch64.Secp256k1
