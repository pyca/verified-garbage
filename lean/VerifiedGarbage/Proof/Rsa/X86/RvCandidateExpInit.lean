module
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Rsa.X86.RvExpInvariant
public import VerifiedGarbage.Proof.Rsa.X86.RvMont

import VerifiedGarbage.Proof.Rsa.X86.RvCandidateSet
import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Bignum.Math

/-! # Exponentiation of a recovery candidate in Montgomery form -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem candExpInit_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m eLen dLen : Nat}
    (h : KS g s0 A liveM AW [wR] V slotsExp s) (zero : A aZ = 0)
    (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1)
    (one : A aO = 2 ^ (64 * g.n) % m) (r2 : A mR2 = 2 ^ (128 * g.n) % m)
    (candidate : V sCand < 100) (baseBound : V sCand + 2 < m)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (limit : 8 * (dLen + eLen) ≤ 16384) :
    WP isa (.seq (candSet g.n) (mmul g.n mG mG mR2)) s (EI g s0 A AW V m (V sCand + 2) (AW wR)
      (8 * (dLen + eLen)) 0) := by
  have positive : 0 < m := by omega
  refine WP.seq (WP.mono (candSet_ok h zero candidate ae ad (by omega)) fun s1 h1 => ?_)
  have mr1 := h1.montReady (m := m) (by simp [liveExp]) (by simp [slotsExp])
    (by simpa only [upd_ne _ _ (by decide : mBase ≠ mY), upd_ne _ _ (by decide : mBase ≠ mG)] using value)
    bound (by simpa only [upd_ne _ _ (by decide : sInv ≠ sCnt)] using inverse)
  refine WP.mono (h1.mmul mr1 (o := mG) (a := mG) (b := mR2)
    (by decide) (by decide) (by decide) (by decide) (by simp [liveExp]) (by simp [liveExp])
    (by simpa only [upd_ne _ _ (by decide : mG ≠ mY), upd_self] using baseBound)
    (by simpa only [upd_ne _ _ (by decide : mR2 ≠ mY), upd_ne _ _ (by decide : mR2 ≠ mG), r2] using
      Nat.mod_lt (2 ^ (128 * g.n)) positive)
    (by decide) (by decide)) fun s2 ⟨G, h2, _, _, glt, gv⟩ => ?_
  have gvalue : G = (V sCand + 2) * 2 ^ (64 * g.n) % m := by
    rw [← Nat.mod_eq_of_lt glt]
    apply VG.Proof.Rsa.g_mont (VG.Proof.Bignum.coprime_pow2 odd _)
      (R2 := 2 ^ (128 * g.n) % m)
    · rw [Nat.mod_mod, ← Nat.pow_add]; congr 2; omega
    · simpa only [upd_ne _ _ (by decide : mG ≠ mY), upd_self,
        upd_ne _ _ (by decide : mR2 ≠ mY), upd_ne _ _ (by decide : mR2 ≠ mG), r2] using gv
  have initial : EI g s0 A AW V m (V sCand + 2) (AW wR) (8 * (dLen + eLen)) 0 s2 := by
    refine h2.mono (fun j hj => ⟨by simp [hj], ?_⟩) (fun j hj => ⟨hj, ?_⟩)
      (fun d hd => ⟨hd, ?_⟩)
    · simp only [AE, Nat.pow_zero, Nat.mod_one, Nat.one_mul, Nat.pow_one, upd]
      split
      · exact gvalue
      · split
        · exact one
        · rfl
    · simp only [Nat.pow_zero, Nat.div_one]
    · simp only [Nat.sub_zero]
  exact initial

end VG.Proof.Rsa.X86.Recover
