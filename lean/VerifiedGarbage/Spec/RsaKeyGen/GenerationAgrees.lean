module

public import VerifiedGarbage.Spec.RsaKeyGen.Generation

/-!
# The RSA prime search is FIPS 186-5's

**Trusted** (its statements; their proofs are checked). `vg_rsa_generate`
runs `primeSearch` for each prime (`keySearch`, `KeySearchContract.lean`), over
the host's refilled tapes. This file proves that `primeSearch` is the search for a
prime of FIPS 186-5 Appendix A.1.3 steps 4 and 5, `generatePrime`, on the
stream of random octets the host hands out, so that `generatePrime` is what
the search is required to compute: a reviewer reads `generatePrime`
(`RsaKeyGen.lean`) and the statements here, not `primeSearch`.

`searchFrom remaining s` is `generatePrime`'s loop with `remaining` counted
rejections left, on the stream `s`; from the state `primeInit` writes it is
`generatePrime` (`searchFrom_init`). A call of the search on a tape `rand`
that the stream `rand ++ t` continues, for any `t`, agrees with it
(`primeSearch_agrees`, `SearchAgrees`):

* if it accepts the prime `c`, having consumed `used` octets, the loop finds
  `c` on the stream, and reads exactly those `used` octets;
* if it asks for more entropy, with `rem` rejections left, the loop on the
  stream is the loop with `rem` left on the stream after the `used` octets
  consumed: the next call, on a tape `Entropy.Refill` gives (the octets after
  the first `used`, then fresh ones: still the start of the stream), goes on
  where this one stopped;
* if it is exhausted, either the loop on the stream fails with
  `tooManyIterations` after the `used` octets, or the search ran into the
  entropy budget: the loop is the loop with some rejections left on the stream
  after the `used` octets, which has at least `primeEntropy` octets more, and
  whose next candidate does not finish within them. That is the one way the search fails where
  `generatePrime` may not.

`used` is never more than the tape (`primeSearch_used_le`). Chained over the
calls of a search from `primeInit`, each on a tape the last call's `Refill`
gives, the prime the last call accepts is `generatePrime`'s on the stream of
every octet the host handed out, whatever octets follow it.
-/

@[expose] public section

namespace VG.Spec.RsaKeyGen

/-- `generatePrime`'s loop (A.1.3 steps 4 and 5) for a prime of `pLen` octets,
for the public exponent `eB`, not too close to the prime `pB` (none if empty),
with `remaining` of its `primeLimit` rejected candidates left, on the stream
`s`. -/
def searchFrom (pLen : Nat) (eB pB : List Byte) (remaining : Nat) (s : Rand) :
    Option (Except Failure Nat × Rand) :=
  loop (primeStep (8 * pLen) (Rsa.os2ip eB) (otherPrime pB))
    (primeLimit (8 * pLen) (Rsa.os2ip eB) - remaining) s

/-- What a call of the search with `remaining` rejected candidates left, which
returned `r`, says of `searchFrom` on the stream `s` its tape starts. -/
def SearchAgrees (pLen : Nat) (eB pB : List Byte) (remaining : Nat) (s : Rand)
    (r : PrimeSearchResult) : Prop :=
  match r.outcome with
  | .accepted c => searchFrom pLen eB pB remaining s = some (.ok c, s.drop r.used)
  | .entropy rem _ => 0 < rem ∧ rem ≤ remaining ∧
      searchFrom pLen eB pB remaining s = searchFrom pLen eB pB rem (s.drop r.used)
  | .exhausted =>
      searchFrom pLen eB pB remaining s = some (.error .tooManyIterations, s.drop r.used) ∨
      ∃ rem, 0 < rem ∧
        searchFrom pLen eB pB remaining s = searchFrom pLen eB pB rem (s.drop r.used) ∧
        primeEntropy pLen ≤ (s.drop r.used).length ∧
        candidateOp pLen eB pB ((s.drop r.used).take (primeEntropy pLen)) = none

/-! ## Reading from the front -/

/-- `f` reads its octets from the front: what it returns from `r` it returns
from any extension of `r`, followed by the extension, and what it leaves of
`r` is a suffix of `r`. -/
private def Reads {β : Type} (f : Rand → Option (β × Rand)) : Prop :=
  ∀ r t b rest, f r = some (b, rest) → f (r ++ t) = some (b, rest ++ t) ∧ rest <:+ r

private theorem draw_reads (len : Nat) : Reads (draw len) := by
  intro r t x rest h
  unfold draw at h ⊢
  dsimp only at h ⊢
  split at h
  · rename_i hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hle : len ≤ r.length := by rw [List.length_take] at hl; omega
    rw [List.take_append_of_le_length hle, ite_eq_left hl, List.drop_append_of_le_length hle]
    exact ⟨rfl, List.drop_suffix len r⟩
  · simp at h

private theorem draw_length {len : Nat} {r rest : Rand} {x : Nat}
    (h : draw len r = some (x, rest)) : rest.length + len = r.length := by
  unfold draw at h
  dsimp only at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rw [List.length_take] at hl
    rw [List.length_drop]; omega
  · simp at h

private theorem loop_reads {σ α : Type} {step : σ → Rand → Option ((α ⊕ σ) × Rand)}
    (hs : ∀ s, Reads (step s)) (s : σ) (r t : Rand) (a : α) (rest : Rand)
    (h : loop step s r = some (a, rest)) :
    loop step s (r ++ t) = some (a, rest ++ t) ∧ rest <:+ r := by
  rw [loop] at h ⊢
  match hst : step s r with
  | none => rw [hst] at h; simp at h
  | some (.inl a', r') =>
    rw [hst] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := hs s r t _ _ hst
    rw [h1]
    exact ⟨rfl, h2⟩
  | some (.inr s', r') =>
    rw [hst] at h
    obtain ⟨h1, h2⟩ := hs s r t _ _ hst
    rw [h1]
    simp only at h ⊢
    split at h
    · rename_i hlt
      obtain ⟨h3, h4⟩ := loop_reads hs s' r' t a rest h
      rw [ite_eq_left (by simp only [List.length_append]; omega)]
      exact ⟨h3, h4.trans h2⟩
    · simp at h
termination_by r.length

private theorem mrStep_reads (w checks a m : Nat) (s : Nat × Nat) :
    Reads (mrStep w checks a m s) := by
  intro r t b rest h
  obtain ⟨i, u⟩ := s
  unfold mrStep at h ⊢
  simp only at h ⊢
  split at h
  · rename_i hc
    rw [ite_eq_left hc]
    match hd : draw (witnessBytes w) r with
    | none => rw [hd] at h; simp at h
    | some (x, r1) =>
      obtain ⟨hd', hsuf⟩ := draw_reads _ r t _ _ hd
      rw [hd] at h
      rw [hd']
      simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
      split at h <;> rename_i hmr <;> simp only [hmr, ↓reduceIte] <;>
        simp only [pure, Option.some.injEq] at h <;> cases h <;> exact ⟨rfl, hsuf⟩
  · rename_i hc
    rw [ite_eq_right hc]
    simp only [Option.some.injEq] at h
    cases h
    exact ⟨rfl, List.suffix_refl _⟩

private theorem primalityTest_reads (w : Nat) : Reads (primalityTest w) := by
  intro r t b rest h
  unfold primalityTest at h ⊢
  split at h
  · rename_i h1
    rw [ite_eq_left h1]
    simp only [Option.some.injEq] at h
    cases h
    exact ⟨rfl, List.suffix_refl _⟩
  · rename_i h1
    rw [ite_eq_right h1]
    split at h
    · rename_i h2
      rw [ite_eq_left h2]
      simp only [Option.some.injEq] at h
      cases h
      exact ⟨rfl, List.suffix_refl _⟩
    · rename_i h2
      rw [ite_eq_right h2]
      split at h
      · rename_i h3
        rw [ite_eq_left h3]
        simp only [Option.some.injEq] at h
        cases h
        exact ⟨rfl, List.suffix_refl _⟩
      · rename_i h3
        rw [ite_eq_right h3]
        exact loop_reads (mrStep_reads _ _ _ _) _ r t b rest h

/-- `candidateStep` reads from the front, and reads at least its candidate's
`bits / 8` octets. -/
theorem candidateStep_reads {bits e : Nat} {p : Option Nat} {r t rest : Rand}
    {b : Candidate} (h : candidateStep bits e p r = some (b, rest)) :
    candidateStep bits e p (r ++ t) = some (b, rest ++ t) ∧ rest <:+ r ∧
      rest.length + bits / 8 ≤ r.length := by
  unfold candidateStep at h ⊢
  match hd : draw (bits / 8) r with
  | none => rw [hd] at h; simp at h
  | some (x, r1) =>
    obtain ⟨hd', hsuf⟩ := draw_reads _ r t _ _ hd
    have hlen := draw_length hd
    rw [hd] at h
    rw [hd']
    simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
    split at h
    · rename_i hcl
      rw [ite_eq_left hcl]
      simp only [pure, Option.some.injEq] at h
      cases h
      exact ⟨rfl, hsuf, by omega⟩
    · rename_i hcl
      rw [ite_eq_right hcl]
      split at h
      · rename_i hg
        rw [ite_eq_left hg]
        match hpt : primalityTest (candidate bits x) r1 with
        | none => rw [hpt] at h; simp at h
        | some (prime, r2) =>
          obtain ⟨hpt', hsuf2⟩ := primalityTest_reads _ r1 t _ _ hpt
          rw [hpt] at h
          rw [hpt']
          simp only [Option.bind_some] at h ⊢
          have hl2 := hsuf2.length_le
          split at h <;> rename_i hpr <;> simp only [hpr, ↓reduceIte] <;>
            simp only [pure, Option.some.injEq] at h <;> cases h <;>
            exact ⟨rfl, hsuf2.trans hsuf, by omega⟩
      · rename_i hg
        rw [ite_eq_right hg]
        simp only [Bool.false_eq_true, ↓reduceIte, pure, Option.some.injEq] at h ⊢
        cases h
        exact ⟨rfl, hsuf, by omega⟩

/-! ## The search -/

/-- From the state `primeInit` writes, `primeLimit` rejected candidates left,
`searchFrom` is `generatePrime`. -/
theorem searchFrom_init {pLen : Nat} {eB pB : List Byte} (hp : primeLenValid pLen)
    (s : Rand) :
    searchFrom pLen eB pB (primeLimit (8 * pLen) (Rsa.os2ip eB)) s =
      generatePrime (8 * pLen) (Rsa.os2ip eB) (otherPrime pB) s := by
  obtain ⟨h1, -, h3⟩ := hp
  rw [searchFrom, Nat.sub_self, generatePrime, ite_eq_right (by omega)]

/-- The search consumes no more than its tape. -/
theorem primeSearch_used_le (pLen : Nat) (eB pB : List Byte) (remaining : Nat) (rand : Rand) :
    (primeSearch pLen eB pB remaining rand).used ≤ rand.length := by
  rw [primeSearch]
  split
  · exact Nat.zero_le _
  · simp only
    split
    · split <;> exact Nat.zero_le _
    · rename_i rest _
      simp only
      omega
    · rename_i rest _
      split
      · rename_i hlt
        have := primeSearch_used_le pLen eB pB remaining rest
        simp only [Entropy.Result.consume]
        omega
      · exact Nat.zero_le _
    · rename_i rest _
      split
      · rename_i hlt
        have := primeSearch_used_le pLen eB pB (remaining - 1) rest
        simp only [Entropy.Result.consume]
        omega
      · exact Nat.zero_le _
termination_by rand.length

private theorem drop_of_suffix {rest rand : Rand} (h : rest <:+ rand) (t : Rand) :
    (rand ++ t).drop (rand.length - rest.length) = rest ++ t := by
  obtain ⟨u, rfl⟩ := h
  simp

private theorem agrees_consume {pLen : Nat} {eB pB : List Byte} {remaining remaining' n : Nat}
    {s s' : Rand} {prior : List Nat} {r : PrimeSearchResult} (hs : s.drop n = s')
    (heq : searchFrom pLen eB pB remaining s = searchFrom pLen eB pB remaining' s')
    (hle : remaining' ≤ remaining) (h : SearchAgrees pLen eB pB remaining' s' r) :
    SearchAgrees pLen eB pB remaining s (r.consume n prior) := by
  have hd : s.drop (r.consume n prior).used = s'.drop r.used := by
    rw [← hs, List.drop_drop]; rfl
  unfold SearchAgrees at h ⊢
  rw [hd, heq]
  simp only [Entropy.Result.consume]
  split at h
  · exact h
  · exact ⟨h.1, Nat.le_trans h.2.1 hle, h.2.2⟩
  · exact h

/-- **The search is FIPS 186-5's.** A call of `primeSearch` for a prime of a
valid length, with `remaining` rejected candidates left (at least one, at
most `primeLimit`), on the tape `rand`, agrees with `searchFrom` on every
stream `rand ++ t` (`SearchAgrees`). -/
theorem primeSearch_agrees {pLen : Nat} {eB pB : List Byte} (hp : primeLenValid pLen)
    (remaining : Nat) (rand t : Rand) (h0 : 0 < remaining)
    (hl : remaining ≤ primeLimit (8 * pLen) (Rsa.os2ip eB)) :
    SearchAgrees pLen eB pB remaining (rand ++ t) (primeSearch pLen eB pB remaining rand) := by
  have hbits : 0 < 8 * pLen / 8 := by obtain ⟨h1, -⟩ := hp; omega
  rw [primeSearch, ite_eq_right (by omega)]
  simp only
  have hS : searchFrom pLen eB pB remaining (rand ++ t) =
      loop (primeStep (8 * pLen) (Rsa.os2ip eB) (otherPrime pB))
        (primeLimit (8 * pLen) (Rsa.os2ip eB) - remaining) (rand ++ t) := rfl
  match hc : candidateOp pLen eB pB rand with
  | none =>
    simp only
    split
    · -- The budget: the candidate did not finish within `primeEntropy` octets.
      rename_i hE
      unfold SearchAgrees
      simp only [List.drop_zero]
      refine Or.inr ⟨remaining, h0, rfl, by simp only [List.length_append]; omega, ?_⟩
      rw [List.take_append_of_le_length hE]
      match hc' : candidateOp pLen eB pB (rand.take (primeEntropy pLen)) with
      | none => rfl
      | some (b, rest) =>
        have := (candidateStep_reads (t := rand.drop (primeEntropy pLen)) hc').1
        rw [List.take_append_drop] at this
        unfold candidateOp at hc
        rw [hc] at this
        simp at this
    · unfold SearchAgrees
      simp only [List.drop_zero]
      exact ⟨h0, Nat.le_refl _, trivial⟩
  | some (.prime c, rest) =>
    obtain ⟨h1, h2, -⟩ := candidateStep_reads (t := t) hc
    unfold SearchAgrees
    simp only
    rw [drop_of_suffix h2, hS, loop]
    simp only [primeStep, bind]
    rw [h1]
    rfl
  | some (.close, rest) =>
    obtain ⟨h1, h2, h3⟩ := candidateStep_reads (t := t) hc
    simp only
    rw [dite_eq_left (by omega)]
    refine agrees_consume (drop_of_suffix h2 t) ?_ (Nat.le_refl _)
      (primeSearch_agrees hp remaining rest t h0 hl)
    rw [hS, loop]
    simp only [primeStep, bind]
    rw [h1]
    simp only [Option.bind_some, pure]
    rw [ite_eq_left (by simp only [List.length_append]; omega)]
    rfl
  | some (.rejected, rest) =>
    obtain ⟨h1, h2, h3⟩ := candidateStep_reads (t := t) hc
    simp only
    rw [dite_eq_left (by omega)]
    have hstep : searchFrom pLen eB pB remaining (rand ++ t) =
        if primeLimit (8 * pLen) (Rsa.os2ip eB) ≤
            primeLimit (8 * pLen) (Rsa.os2ip eB) - remaining + 1 then
          some (.error .tooManyIterations, rest ++ t)
        else loop (primeStep (8 * pLen) (Rsa.os2ip eB) (otherPrime pB))
          (primeLimit (8 * pLen) (Rsa.os2ip eB) - remaining + 1) (rest ++ t) := by
      rw [hS, loop]
      simp only [primeStep, bind]
      rw [h1]
      simp only [Option.bind_some, pure]
      by_cases hlim : primeLimit (8 * pLen) (Rsa.os2ip eB) ≤
          primeLimit (8 * pLen) (Rsa.os2ip eB) - remaining + 1
      · simp only [hlim, ↓reduceIte]
      · simp only [hlim, ↓reduceIte]
        rw [ite_eq_left (by simp only [List.length_append]; omega)]
    by_cases h1r : remaining = 1
    · -- The last rejection allowed: both fail with too many tries.
      subst h1r
      rw [primeSearch, ite_eq_left rfl]
      unfold SearchAgrees
      simp only [Entropy.Result.consume, Nat.add_zero]
      left
      rw [hstep, ite_eq_left (by omega), drop_of_suffix h2]
    · refine agrees_consume (drop_of_suffix h2 t) ?_ (Nat.sub_le _ _)
        (primeSearch_agrees hp (remaining - 1) rest t (by omega) (by omega))
      rw [hstep, ite_eq_right (by omega)]
      unfold searchFrom
      congr 1
      omega
termination_by rand.length

end VG.Spec.RsaKeyGen
