import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# RSA key generation: what every generated key satisfies

For every key `RsaKeyGen.generate` returns, whatever the randomness
(`generate_ok`):

* it passes the key check (`keyValid`, what `RSA_check_key` checks) and the
  pairwise consistency test (`pairwiseOk`), and has the public exponent it
  was asked for and a modulus of `nlen` bits, the size it was asked for
  rounded down to a multiple of 128 bits, from 512 to 8192;
* its primes have `nlen / 2` bits, of which the two most significant are set
  (so they are above `√2 · 2^(nlen/2 − 1)`), and are odd (`PrimeShape`);
* `p > q`, and `p − q > 2^(nlen/2 − 100)`;
* `gcd(p − 1, e) = gcd(q − 1, e) = 1`;
* `d > 2^(nlen/2)`, and `d e ≡ 1 (mod lcm(p − 1, q − 1))`.

None of this depends on the primality test: the bounds hold of every
candidate accepted, and the checks are part of the generation.
-/

namespace VG.Spec.RsaKeyGen

/-- An accepted candidate of `bits` bits: odd, below `2^bits`, with its two
most significant bits set. -/
def PrimeShape (bits c : Nat) : Prop := c % 2 = 1 ∧ 3 * 2 ^ (bits - 2) ≤ c ∧ c < 2 ^ bits

/-! ## Loops -/

/-- What every result of an iteration that finishes satisfies, the loop's
result satisfies. -/
theorem loop_inl {σ α : Type} {step : σ → Rand → Option ((α ⊕ σ) × Rand)} (P : α → Prop)
    (hstep : ∀ s r a r', step s r = some (.inl a, r') → P a) :
    ∀ s r a r', loop step s r = some (a, r') → P a := by
  intro s r
  induction r using (measure List.length).wf.induction generalizing s with
  | h r ih =>
    intro a r' h
    rw [loop] at h
    split at h
    · cases h
    · cases h
      exact hstep _ _ _ _ (by assumption)
    · split at h
      · exact ih _ (by assumption) _ _ _ h
      · cases h

/-! ## Candidates -/

theorem candidate_shape {bits : Nat} (hb : 2 ≤ bits) (x : Nat) :
    PrimeShape bits (candidate bits x) := by
  unfold candidate PrimeShape
  have h4 : 2 ^ bits = 2 ^ (bits - 2) * 4 := by
    rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]; congr 1; omega
  have hpos := Nat.two_pow_pos (bits - 2)
  refine ⟨?_, ?_, ?_⟩
  · rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.or_mod_two_pow]
    rcases Nat.mod_two_eq_zero_or_one ((x % 2 ^ bits ||| 3 * 2 ^ (bits - 2))) with h | h <;>
      simp [h]
  · exact Nat.le_trans (Nat.right_le_or) (Nat.left_le_or)
  · exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _)) (by omega))
      (Nat.one_lt_two_pow (by omega))

/-- An accepted candidate: shaped, not too close to `p`, and with
`gcd(c − 1, e) = 1`. -/
theorem candidateStep_prime {bits e : Nat} {p : Option Nat} {r : Rand} {c : Nat} {r' : Rand}
    (h : candidateStep bits e p r = some (.prime c, r')) :
    (∃ x, c = candidate bits x) ∧ tooClose bits p c = false ∧ Nat.gcd (c - 1) e = 1 := by
  simp only [candidateStep, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨x, r₁⟩, -, h⟩ := h
  simp only at h
  split at h
  · simp [pure] at h
  rename_i hclose
  split at h
  · rename_i hcond
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨b, r₂⟩, -, h⟩ := h
    split at h
    · simp only [pure, Option.some.injEq, Prod.mk.injEq, Candidate.prime.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at hcond
      exact ⟨⟨x, rfl⟩, by simpa using hclose, hcond.2⟩
    · simp [pure] at h
  · simp [pure] at h

/-! ## Primes -/

/-- What `generatePrime` returns, if a prime. -/
def PrimeOk (bits e : Nat) (p : Option Nat) (c : Nat) : Prop :=
  PrimeShape bits c ∧ tooClose bits p c = false ∧ Nat.gcd (c - 1) e = 1

theorem generatePrime_ok {bits e : Nat} {p : Option Nat} {r : Rand} {c : Nat} {r' : Rand}
    (h : generatePrime bits e p r = some (.ok c, r')) : PrimeOk bits e p c := by
  unfold generatePrime at h
  split at h
  · cases h
  rename_i hb
  refine loop_inl (fun res => ∀ c, res = .ok c → PrimeOk bits e p c) ?_ 0 r _ r' h c rfl
  intro tries r a r' hs c hc
  subst hc
  simp only [primeStep, bind, Option.bind_eq_some_iff] at hs
  obtain ⟨⟨res, r₁⟩, hres, hs⟩ := hs
  cases res with
  | prime c' =>
    simp only [pure, Option.some.injEq, Prod.mk.injEq, Sum.inl.injEq, Except.ok.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    obtain ⟨⟨x, rfl⟩, hclose, hgcd⟩ := candidateStep_prime hres
    exact ⟨candidate_shape (by omega) x, hclose, hgcd⟩
  | close => simp [pure] at hs
  | rejected =>
    simp only at hs
    split at hs <;> simp [pure] at hs

/-! ## Keys -/

theorem inverse_mul {a m x : Nat} (h : Rsa.inverse a m = some x) : a * x % m = 1 := by
  unfold Rsa.inverse at h
  simp only at h
  split at h
  · cases h; assumption
  · cases h

/-- What `keyFromPrimes` returns, if a key. -/
theorem keyFromPrimes_ok {nlen e p q : Nat} {k : Key}
    (h : keyFromPrimes nlen e p q = .inl (.ok k)) :
    k.e = e ∧ keyValid k = true ∧ bitLength k.n = nlen ∧ 2 ^ (nlen / 2) < k.d ∧
      e * k.d % Nat.lcm (k.p - 1) (k.q - 1) = 1 ∧
      (k.p, k.q) = (if p < q then (q, p) else (p, q)) := by
  unfold keyFromPrimes at h
  generalize hpq : (if p < q then (q, p) else (p, q)) = pq at h
  obtain ⟨p', q'⟩ := pq
  simp only at h
  split at h
  · cases h
  rename_i d hd
  split at h
  · cases h
  rename_i hdlarge
  split at h
  · cases h
  rename_i qInv hq
  split at h
  · rename_i hk
    simp only [Sum.inl.injEq, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, by simpa using hk.2, hk.1, show 2 ^ (nlen / 2) < d by omega, inverse_mul hd, rfl⟩
  · cases h

/-- What `keyStep` returns, if a key: `keyFromPrimes` of two primes, the
second not too close to the first. -/
theorem keyStep_ok {nlen e : Nat} {r : Rand} {k : Key} {r' : Rand}
    (h : keyStep nlen e () r = some (.inl (.ok k), r')) :
    ∃ p q, PrimeOk (nlen / 2) e none p ∧ PrimeOk (nlen / 2) e (some p) q ∧
      keyFromPrimes nlen e p q = .inl (.ok k) := by
  simp only [keyStep, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨rp, r₁⟩, hp, h⟩ := h
  cases rp with
  | error f => simp [pure] at h
  | ok p =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨rq, r₂⟩, hq, h⟩ := h
    cases rq with
    | error f => simp [pure] at h
    | ok q =>
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨p, q, generatePrime_ok hp, generatePrime_ok hq, h.1⟩

/-- What a key `generateOnce` returns satisfies, but for the pairwise
consistency test. -/
def KeyOk (nlen e : Nat) (k : Key) : Prop :=
  k.e = e ∧ keyValid k = true ∧ bitLength k.n = nlen ∧
    PrimeShape (nlen / 2) k.p ∧ PrimeShape (nlen / 2) k.q ∧
    k.q < k.p ∧ 2 ^ (nlen / 2 - 100) < k.p - k.q ∧
    Nat.gcd (k.p - 1) e = 1 ∧ Nat.gcd (k.q - 1) e = 1 ∧ 2 ^ (nlen / 2) < k.d ∧
    e * k.d % Nat.lcm (k.p - 1) (k.q - 1) = 1

theorem keyStep_keyOk {nlen e : Nat} {r : Rand} {k : Key} {r' : Rand}
    (h : keyStep nlen e () r = some (.inl (.ok k), r')) : KeyOk nlen e k := by
  obtain ⟨p, q, ⟨hp, -, hpg⟩, ⟨hq, hclose, hqg⟩, hk⟩ := keyStep_ok h
  obtain ⟨he, hv, hn, hd, hde, hpq⟩ := keyFromPrimes_ok hk
  simp only [tooClose, absDiff] at hclose
  replace hclose := Nat.lt_of_not_le (of_decide_eq_false hclose)
  refine ⟨he, hv, hn, ?_⟩
  split at hpq <;> simp only [Prod.mk.injEq] at hpq <;> obtain ⟨hkp, hkq⟩ := hpq <;>
    rw [hkp, hkq] at hde ⊢
  · rename_i hlt
    split at hclose <;> exact ⟨hq, hp, hlt, by omega, hqg, hpg, hd, hde⟩
  · rename_i hge
    split at hclose
    · have : p ≠ q := by
        intro hpq; subst hpq; simp at hclose
      exact ⟨hp, hq, by omega, by omega, hpg, hqg, hd, hde⟩
    · omega

theorem generateOnce_ok {nlen e : Nat} {r : Rand} {k : Key} {r' : Rand}
    (h : generateOnce nlen e r = some (.ok k, r')) : KeyOk nlen e k :=
  loop_inl (fun res => ∀ k, res = .ok k → KeyOk nlen e k)
    (fun _ _ _ _ hs k hk => by subst hk; exact keyStep_keyOk hs) () r _ r' h k rfl

/-! ## `generate` -/

theorem params_ok {bits e nlen : Nat} (h : params bits e = some nlen) :
    exponentValid e = true ∧ minBits ≤ nlen ∧ nlen ≤ maxBits ∧ nlen % 128 = 0 ∧ nlen ≤ bits := by
  unfold params modulusBits at h
  split at h
  · rename_i he
    simp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact ⟨he, by omega, by omega, by omega, by omega⟩
  · cases h

theorem generate_attempts_ok {nlen e : Nat} {k : Key} :
    ∀ left r, generate.attempts e nlen left r = some (.ok k) → KeyOk nlen e k ∧ pairwiseOk k = true
  | 0, _, h => by simp [generate.attempts] at h
  | left + 1, r, h => by
    unfold generate.attempts at h
    split at h
    · cases h
    · exact generate_attempts_ok left _ h
    · cases h
    · rename_i hk
      split at h
      · cases h
        exact ⟨generateOnce_ok hk, by assumption⟩
      · cases h

/-- Every key `generate` returns passes the key check and the pairwise
consistency test, has the public exponent asked for, a modulus of the size
asked for rounded down to a multiple of 128 bits (from 512 to 8192), primes
of half that size with their two most significant bits set, more than
`2^(nlen/2 − 100)` apart, and `d > 2^(nlen/2)` an inverse of `e` modulo
`lcm(p − 1, q − 1)`. -/
theorem generate_ok {bits e : Nat} {rand : Rand} {k : Key}
    (h : generate bits e rand = some (.ok k)) :
    ∃ nlen, params bits e = some nlen ∧ exponentValid e = true ∧ minBits ≤ nlen ∧
      nlen ≤ maxBits ∧ nlen % 128 = 0 ∧ nlen ≤ bits ∧ KeyOk nlen e k ∧ pairwiseOk k = true := by
  unfold generate at h
  split at h
  · cases h
  · rename_i nlen hp
    obtain ⟨he, h1, h2, h3, h4⟩ := params_ok hp
    exact ⟨nlen, hp, he, h1, h2, h3, h4, generate_attempts_ok 4 rand h⟩

end VG.Spec.RsaKeyGen
