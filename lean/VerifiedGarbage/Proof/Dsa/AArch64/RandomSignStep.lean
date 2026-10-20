module

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignAttempt
public import VerifiedGarbage.Proof.Dsa.RandomSignTraceResult
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRunning
import VerifiedGarbage.Proof.Framework.Omega

/-! Public status and continuation facts after one signing attempt. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def RandomSignStepPost {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (used fuel : Nat) (t : State) : Prop :=
  (∃ remaining, RandomSignRunning h hq (used + (randomSignDraw (randomInput s) used).used) remaining t) ∧
  word t.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 (randomSignAttemptStatus (randomInput s) used fuel) ∧
  (randomSignAttemptStatus (randomInput s) used fuel = 4 →
    RandomSignRunning h hq (used + (randomSignDraw (randomInput s) used).used) (fuel - 1) t)

theorem random_sign_step (v : Backend) {s t : State} {h : RandomSignABI v.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hf : 0 < fuel) (hb : fuel < 2 ^ 64) :
    WP isa (RandomSign.attempt (randomSignerName v) (SignVerify.sign v.mul)) t (RandomSignStepPost h hq used fuel) := by
  refine WP.mono (random_sign_attempt v hr hf hb) fun u hu => ?_
  cases hd : (randomSignDraw (randomInput s) used).scalar with
  | none =>
    simp only [RandomSignAttemptPost, hd] at hu
    obtain ⟨hr', hs⟩ := hu
    refine ⟨⟨fuel, hr'⟩, ?_, ?_⟩
    · simpa only [randomSignAttemptStatus, hd] using hs
    · intro he
      obtain ⟨_, k, hk, _⟩ := random_sign_attempt_continue hf he
      rw [hd] at hk
      contradiction
  | some k =>
    simp only [RandomSignAttemptPost, hd] at hu
    obtain ⟨hr', hs, _⟩ := hu
    refine ⟨⟨_, hr'⟩, ?_, ?_⟩
    · unfold randomSignAttemptStatus
      rw [hd]
      change word u.mem (randomBase s) Random.oStatus =
        BitVec.ofNat 64 (if (randomSingleResult s k).isSome then 1 else if fuel = 1 then 0 else 4)
      cases hk : (randomSingleResult s k).isSome <;> by_cases hn : fuel = 1 <;>
        simp only [hk, hn, Bool.false_eq_true, ite_true, ite_false] at hs ⊢ <;> exact hs
    · intro he
      obtain ⟨_, l, hl, hsign⟩ := random_sign_attempt_continue hf he
      rw [hd, Option.some.injEq] at hl
      subst l
      change randomSingleResult s k = none at hsign
      simpa only [hsign, Option.isSome_none, Bool.false_eq_true, ite_false] using hr'

theorem RandomSignStepPost.congr {extra : Nat} {s t u : State} {h : RandomSignABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hp : RandomSignStepPost h hq used fuel t) (hm : u.mem = t.mem)
    (hk : Keep [.x0, .x4] t u) : RandomSignStepPost h hq used fuel u := by
  obtain ⟨⟨remaining, hr⟩, hs, hc⟩ := hp
  exact ⟨⟨remaining, hr.congr hm hk⟩, by rw [hm]; exact hs, fun hh => (hc hh).congr hm hk⟩

end VG.Proof.Dsa.AArch64
