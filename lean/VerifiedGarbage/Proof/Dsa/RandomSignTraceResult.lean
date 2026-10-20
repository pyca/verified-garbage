module
public import VerifiedGarbage.Proof.Dsa.RandomSignRemaining

import VerifiedGarbage.Proof.Dsa.RandomSignTrace
import VerifiedGarbage.Proof.Framework.Omega

/-! A signing attempt's status and continuation are determined by its public trace. -/
@[expose] public section
namespace VG.Proof.Dsa
open VG.Spec.Dsa

def randomSignAttemptStatus (p : RandomSignInput) (used fuel : Nat) : Nat :=
  match (randomSignDraw p used).scalar with
  | none => Random.sampleStatus (randomSignDraw p used)
  | some k => if (signBytes p.pLen p.qLen p.key (encodeBE p.qLen k) p.digest).isSome then 1
      else if fuel = 1 then 0 else 4

theorem random_sign_attempt_status_bound (p : RandomSignInput) (used fuel : Nat) :
    randomSignAttemptStatus p used fuel ≤ 4 := by
  unfold randomSignAttemptStatus
  split
  next hc => simp only [Random.sampleStatus, hc]; split <;> decide
  next => split
          · decide
          · split <;> decide

theorem random_sign_attempt_continue {p : RandomSignInput} {used fuel : Nat}
    (hf : 0 < fuel) (h : randomSignAttemptStatus p used fuel = 4) :
    1 < fuel ∧ ∃ k, (randomSignDraw p used).scalar = some k ∧
      signBytes p.pLen p.qLen p.key (encodeBE p.qLen k) p.digest = none := by
  unfold randomSignAttemptStatus at h
  split at h
  next hc =>
    simp only [Random.sampleStatus, hc] at h
    split at h <;> contradiction
  next k hc =>
    cases hs : signBytes p.pLen p.qLen p.key (encodeBE p.qLen k) p.digest with
    | some sig => simp only [hs, Option.isSome_some, ite_true] at h; contradiction
    | none =>
      simp only [hs, Option.isSome_none, Bool.false_eq_true, ite_false] at h
      have hn : fuel ≠ 1 := by intro he; rw [ite_eq_left he] at h; contradiction
      exact ⟨by omega, k, hc, hs⟩

theorem random_sign_attempt_status_agree {p r : RandomSignInput} {used fuel : Nat}
    (htrace : (randomSignRemaining p used (fuel + 1)).trace = (randomSignRemaining r used (fuel + 1)).trace)
    (hscalar : (randomSignDraw p used).scalar.isSome = (randomSignDraw r used).scalar.isSome)
    (hstatus : Random.sampleStatus (randomSignDraw p used) = Random.sampleStatus (randomSignDraw r used)) :
    randomSignAttemptStatus p used (fuel + 1) = randomSignAttemptStatus r used (fuel + 1) := by
  cases hp : (randomSignDraw p used).scalar with
  | none =>
    cases hr : (randomSignDraw r used).scalar with
    | none => simpa only [randomSignAttemptStatus, hp, hr] using hstatus
    | some l => rw [hp, hr] at hscalar; contradiction
  | some k =>
    cases hr : (randomSignDraw r used).scalar with
    | none => rw [hp, hr] at hscalar; contradiction
    | some l =>
      simp only [randomSignAttemptStatus, hp, hr]
      rw [random_sign_trace_call htrace hp hr]

theorem random_sign_attempt_next_trace {p r : RandomSignInput} {used fuel : Nat}
    (htrace : (randomSignRemaining p used (fuel + 1)).trace = (randomSignRemaining r used (fuel + 1)).trace)
    (hp : randomSignAttemptStatus p used (fuel + 1) = 4)
    (hr : randomSignAttemptStatus r used (fuel + 1) = 4) :
    (randomSignRemaining p (used + (randomSignDraw p used).used) fuel).trace =
      (randomSignRemaining r (used + (randomSignDraw r used).used) fuel).trace := by
  obtain ⟨_, k, hk, hsk⟩ := random_sign_attempt_continue (by omega) hp
  obtain ⟨_, l, hl, hsl⟩ := random_sign_attempt_continue (by omega) hr
  exact random_sign_trace_next htrace hk hl hsk hsl

end VG.Proof.Dsa
