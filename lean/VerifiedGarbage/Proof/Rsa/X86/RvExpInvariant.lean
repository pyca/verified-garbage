module

public import VerifiedGarbage.Proof.Rsa.X86.RvExpStep
import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Bignum.Math

/-! # The exponentiation invariant for a recovery candidate -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

def AE (A : Nat → Nat) (n m b r k : Nat) : Nat → Nat :=
  upd (upd A mY (b ^ (r % 2 ^ k) * 2 ^ (64 * n) % m))
    mG (b ^ (2 ^ k) * 2 ^ (64 * n) % m)

def EI (g : Geo) (s0 : State) (A AW V : Nat → Nat) (m b r c k : Nat) (s : State) : Prop :=
  KS g s0 (AE A g.n m b r k) liveExp (upd AW wRc (r / 2 ^ k)) [wRc, wR]
    (upd V sCnt (c - k)) slotsExp s

theorem expBody_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m b r c k : Nat}
    (h : EI g s0 A AW V m b r c k s)
    (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0)
    (odd : m % 2 = 1) (positive : 0 < m) (one : A aO = 2 ^ (64 * g.n) % m)
    (hk : k < c) (hc : c ≤ 16384) :
    WP isa (expBody g.n) s fun t => EI g s0 A AW V m b r c (k + 1) t ∧
      t.zf = some (decide (c - (k + 1) = 0)) := by
  have vbase : AE A g.n m b r k mBase = m := by
    simpa only [AE, upd_ne _ _ (by decide : mBase ≠ mG),
      upd_ne _ _ (by decide : mBase ≠ mY)] using value
  have vone : AE A g.n m b r k aO = 2 ^ (64 * g.n) % m := by
    simpa only [AE, upd_ne _ _ (by decide : aO ≠ mG),
      upd_ne _ _ (by decide : aO ≠ mY)] using one
  refine WP.mono (expBody_step h vbase bound
    (by simpa only [upd_ne _ _ (by decide : sInv ≠ sCnt)] using inverse)
    (by simpa only [AE, upd_ne _ _ (by decide : mY ≠ mG), upd_self] using
      Nat.mod_lt (b ^ (r % 2 ^ k) * 2 ^ (64 * g.n)) positive)
    (by simpa only [AE, upd_self] using Nat.mod_lt (b ^ (2 ^ k) * 2 ^ (64 * g.n)) positive)
    (by rw [vone]; exact Nat.mod_lt _ positive)
    (by rw [upd_self]; omega) (by rw [upd_self]; omega))
    fun t ⟨Y, G, ht, ylt, glt, yv, gv, zt⟩ => ?_
  have powers := VG.Proof.Rsa.exp_step (VG.Proof.Bignum.coprime_pow2 odd (64 * g.n))
    (g := b) (r := r) (i := k) (Y := AE A g.n m b r k mY)
    (G := AE A g.n m b r k mG)
    (by simp only [AE, upd_ne _ _ (by decide : mY ≠ mG), upd_self])
    (by simp only [AE, upd_self])
    (by rw [upd_self, vone]) ylt yv glt gv
  refine ⟨ht.mono ?_ ?_ ?_, ?_⟩
  · intro j hj
    refine ⟨hj, ?_⟩
    simp only [AE, upd]
    split
    · exact powers.2
    · split
      · exact powers.1
      · rfl
  · intro j hj
    refine ⟨hj, ?_⟩
    simp only [upd, ite_true]
    split
    · rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    · rfl
  · intro d hd
    refine ⟨hd, ?_⟩
    simp only [upd, ite_true]
    split <;> omega
  · rw [upd_self] at zt
    simpa only [Nat.sub_sub, Nat.add_comm 1 k] using zt

end VG.Proof.Rsa.X86.Recover
