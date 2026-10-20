module

public import VerifiedGarbage.Proof.Ffdh.GenerationPolicy

/-! # The native key search, step by step

`keySearch` unfolded once in each of its cases, and a search from an offset
into the tape, `keyTail`, as the controllers' loops track it.
-/

@[expose] public section

namespace VG.Proof.Ffdh.GenerationSearch

open VG.Spec.Ffdh
open VG.Proof.Ffdh

variable {policy : GenerationPolicy}
open VG.Spec.RsaKeyGen (Rand)

/-- The status of the attempt on the first `len` octets of `rand`. -/
def attemptStatus (policy : GenerationPolicy) (a : Parameters) (len : Nat) (rand : Rand) : Nat :=
  keyStatus a (policy.scalar a (rand.take len))

/-- A search's result with `n` more octets consumed before it, and no status. -/
def after (n : Nat) (r : KeySearchResult) : KeySearchResult :=
  { r with used := n + r.used }

/-- The search from octet `used` of the tape, with the budgets `keys` and
`scalars`, counting the octets consumed from the tape's start. -/
def keyTail (policy : GenerationPolicy) (a : Parameters) (len : Nat) (rand : Rand) (used keys scalars : Nat) : KeySearchResult :=
  after used (policy.search a len ⟨keys, scalars⟩ (rand.drop used))

theorem keySearch_exhausted {a : Parameters} {len keys scalars : Nat} {rand : Rand}
    (h : keys = 0 ∨ scalars = 0) : policy.search a len ⟨keys, scalars⟩ rand = ⟨.exhausted, 0, []⟩ := by
  cases policy <;> simp only [GenerationPolicy.search] <;> first | rw [keySearch] | rw [vettedKeySearch]
  all_goals rcases h with rfl | rfl <;> simp

theorem keySearch_short {a : Parameters} {len keys scalars : Nat} {rand : Rand}
    (hk : keys ≠ 0) (hs : scalars ≠ 0) (hr : rand.length < len) :
    policy.search a len ⟨keys, scalars⟩ rand = ⟨.entropy ⟨keys, scalars⟩, 0, []⟩ := by
  cases policy <;> simp only [GenerationPolicy.search] <;> first | rw [keySearch] | rw [vettedKeySearch]
  all_goals simp only [hk, hs, hr, or_self, ite_false, ite_true]

private theorem attempt_of {a : Parameters} {len keys scalars : Nat} {rand : Rand}
    (hk : keys ≠ 0) (hs : scalars ≠ 0) (hr : len ≤ rand.length) :
    policy.search a len ⟨keys, scalars⟩ rand =
      let x := policy.scalar a (rand.take len)
      let status := keyStatus a x
      if status = 1 then ⟨.accepted x (VG.Spec.Rsa.powMod a.g x a.p), len, [1]⟩ else
      if status = 2 then
        if scalars ≤ 1 then ⟨.exhausted, len, [2]⟩ else
          (policy.search a len ⟨keys, scalars - 1⟩ (rand.drop len)).consume len 2
      else if status = 3 then
        if keys ≤ 1 then ⟨.exhausted, len, [3]⟩ else
          (policy.search a len ⟨keys - 1, 128⟩ (rand.drop len)).consume len 3
      else ⟨.exhausted, len, [status]⟩ := by
  cases policy <;> simp only [GenerationPolicy.search, GenerationPolicy.scalar] <;> first | rw [keySearch] | rw [vettedKeySearch]
  all_goals simp only [hk, hs, show ¬rand.length < len by omega, or_self, ite_false]
  all_goals rfl

theorem keySearch_accepted {a : Parameters} {len keys scalars : Nat} {rand : Rand}
    (hk : keys ≠ 0) (hs : scalars ≠ 0) (hr : len ≤ rand.length)
    (h : attemptStatus policy a len rand = 1) :
    policy.search a len ⟨keys, scalars⟩ rand =
      ⟨.accepted (policy.scalar a (rand.take len))
        (VG.Spec.Rsa.powMod a.g (policy.scalar a (rand.take len)) a.p), len, [1]⟩ := by
  rw [attempt_of hk hs hr]
  simp only [attemptStatus] at h
  simp only [h, ite_true]

theorem keySearch_scalar {a : Parameters} {len keys scalars : Nat} {rand : Rand}
    (hk : keys ≠ 0) (hs : scalars ≠ 0) (hr : len ≤ rand.length)
    (h : attemptStatus policy a len rand = 2) :
    policy.search a len ⟨keys, scalars⟩ rand =
      (policy.search a len ⟨keys, scalars - 1⟩ (rand.drop len)).consume len 2 := by
  rw [attempt_of hk hs hr]
  simp only [attemptStatus] at h
  simp only [h, show (2 : Nat) ≠ 1 by decide, ite_false, ite_true]
  by_cases h1 : scalars ≤ 1
  · have h0 : scalars - 1 = 0 := by omega
    simp only [h1, ite_true, h0, keySearch_exhausted (Or.inr rfl), KeySearchResult.consume, Nat.add_zero]
  · simp only [h1, ite_false]

theorem keySearch_public {a : Parameters} {len keys scalars : Nat} {rand : Rand}
    (hk : keys ≠ 0) (hs : scalars ≠ 0) (hr : len ≤ rand.length)
    (h : attemptStatus policy a len rand = 3) :
    policy.search a len ⟨keys, scalars⟩ rand =
      (policy.search a len ⟨keys - 1, 128⟩ (rand.drop len)).consume len 3 := by
  rw [attempt_of hk hs hr]
  simp only [attemptStatus] at h
  simp only [h, show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, ite_false, ite_true]
  by_cases h1 : keys ≤ 1
  · have h0 : keys - 1 = 0 := by omega
    simp only [h1, ite_true, h0, keySearch_exhausted (Or.inl rfl), KeySearchResult.consume, Nat.add_zero]
  · simp only [h1, ite_false]

theorem keySearch_other {a : Parameters} {len keys scalars : Nat} {rand : Rand}
    (hk : keys ≠ 0) (hs : scalars ≠ 0) (hr : len ≤ rand.length)
    (h1 : attemptStatus policy a len rand ≠ 1) (h2 : attemptStatus policy a len rand ≠ 2)
    (h3 : attemptStatus policy a len rand ≠ 3) :
    policy.search a len ⟨keys, scalars⟩ rand = ⟨.exhausted, len, [attemptStatus policy a len rand]⟩ := by
  rw [attempt_of hk hs hr]
  simp only [attemptStatus] at h1 h2 h3 ⊢
  simp only [h1, h2, h3, ite_false]

/-- A key's status is 1, 2 or 3. -/
theorem keyStatus_cases (a : Parameters) (x : Nat) :
    keyStatus a x = 1 ∨ keyStatus a x = 2 ∨ keyStatus a x = 3 := by
  unfold keyStatus
  split
  · exact Or.inr (Or.inl rfl)
  · split
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)

theorem attemptStatus_cases (a : Parameters) (len : Nat) (rand : Rand) :
    attemptStatus policy a len rand = 1 ∨ attemptStatus policy a len rand = 2 ∨ attemptStatus policy a len rand = 3 :=
  keyStatus_cases _ _

/-! ## The search from an offset -/

section Tail

variable {a : Parameters} {len : Nat} {rand : Rand} {used keys scalars : Nat}

theorem keyTail_exhausted (h : keys = 0 ∨ scalars = 0) :
    keyTail policy a len rand used keys scalars = ⟨.exhausted, used, []⟩ := by
  simp only [keyTail, keySearch_exhausted h, after, Nat.add_zero]

theorem keyTail_short (hk : keys ≠ 0) (hs : scalars ≠ 0) (hr : rand.length - used < len) :
    keyTail policy a len rand used keys scalars = ⟨.entropy ⟨keys, scalars⟩, used, []⟩ := by
  simp only [keyTail, keySearch_short hk hs (by rw [List.length_drop]; exact hr),
    after, Nat.add_zero]

theorem keyTail_accepted (hk : keys ≠ 0) (hs : scalars ≠ 0) (hr : len ≤ rand.length - used)
    (h : attemptStatus policy a len (rand.drop used) = 1) :
    keyTail policy a len rand used keys scalars =
      ⟨.accepted (policy.scalar a ((rand.drop used).take len))
        (VG.Spec.Rsa.powMod a.g (policy.scalar a ((rand.drop used).take len)) a.p), used + len, [1]⟩ := by
  simp only [keyTail, keySearch_accepted hk hs (by rw [List.length_drop]; exact hr) h,
    after]

theorem keyTail_scalar (hk : keys ≠ 0) (hs : scalars ≠ 0) (hr : len ≤ rand.length - used)
    (h : attemptStatus policy a len (rand.drop used) = 2) :
    keyTail policy a len rand used keys scalars =
      { keyTail policy a len rand (used + len) keys (scalars - 1) with
        statuses := 2 :: (keyTail policy a len rand (used + len) keys (scalars - 1)).statuses } := by
  simp only [keyTail, keySearch_scalar hk hs (by rw [List.length_drop]; exact hr) h,
    after, KeySearchResult.consume, List.drop_drop, Nat.add_assoc]

theorem keyTail_public (hk : keys ≠ 0) (hs : scalars ≠ 0) (hr : len ≤ rand.length - used)
    (h : attemptStatus policy a len (rand.drop used) = 3) :
    keyTail policy a len rand used keys scalars =
      { keyTail policy a len rand (used + len) (keys - 1) 128 with
        statuses := 3 :: (keyTail policy a len rand (used + len) (keys - 1) 128).statuses } := by
  simp only [keyTail, keySearch_public hk hs (by rw [List.length_drop]; exact hr) h,
    after, KeySearchResult.consume, List.drop_drop, Nat.add_assoc]

/-- The statuses from an offset begin with the attempt's, if there is one. -/
theorem keyTail_statuses_head (hk : keys ≠ 0) (hs : scalars ≠ 0) (hr : len ≤ rand.length - used) :
    (keyTail policy a len rand used keys scalars).statuses.head? =
      some (attemptStatus policy a len (rand.drop used)) := by
  rcases attemptStatus_cases a len (rand.drop used) with h | h | h
  · rw [keyTail_accepted hk hs hr h, h]; rfl
  · rw [keyTail_scalar hk hs hr h, h]; rfl
  · rw [keyTail_public hk hs hr h, h]; rfl

end Tail

end VG.Proof.Ffdh.GenerationSearch
