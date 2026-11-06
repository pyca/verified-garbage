module

public import VerifiedGarbage.Spec.RsaKeyGen.KeySearch
public import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees

/-!
# The RSA key search is `generate`

**Trusted** (its statements; their proofs are checked). `vg_rsa_generate`
is required to compute `keySearch` (`KeySearchContract.lean`), over the
host's refilled tapes. This file proves that `keySearch` is `generate`
(`RsaKeyGen.lean`) on the stream of random octets the host hands out, but
where a candidate does not finish within its search's budget, so that a
reviewer reads `generate` and the statements here, not `keySearch`.

`keyFrom st s` is what is left of `generate` from the search's state `st`,
on the stream `s`: the rest of the current iteration of
`rsa_generate_key_impl`'s loop, from the prime `st` draws with
`st.remaining` rejected candidates left, then the generation's further
iterations and `st.left - 1` more generations. From the state
`vg_rsa_generate_init` writes, it is `generate` (`keyFrom_init`). A call of the
search on a tape `rand` that the stream `rand ++ t` continues, for any `t`,
agrees with it (`keySearch_agrees`, `KeySearchAgrees`), unless the stream
holds, after some point, at least `primeEntropy` octets in which a candidate
does not finish (`BudgetHit`):

* if it returns a key, or a failed check, so does `keyFrom`;
* if it asks for more entropy, `keyFrom` is `keyFrom` from the state it
  leaves, on the stream after the `used` octets it consumed: the next call,
  on a tape `Entropy.Refill` gives, goes on where this one stopped;
* if it is exhausted, `keyFrom` fails with `tooManyIterations`.

Chained over the calls of a search from `vg_rsa_generate_init`, each on a
tape the last call's `Refill` gives, the key the last call returns is
`generate`'s on the stream of every octet the host handed out, whatever
octets follow it.
-/

@[expose] public section

namespace VG.Spec.RsaKeyGen

open VG.Spec.Rsa (os2ip i2osp)

/-! ## What is left of `generate` -/

/-- The rest of an iteration of `rsa_generate_key_impl`'s loop once `p` is
found (its octets `pB`): `q`'s search, with `remaining` rejected candidates
left, on the stream `s`, then the key from the primes' octets. -/
def stepQ (pLen : Nat) (eB pB : List Byte) (remaining : Nat) (s : Rand) :
    Option ((Except Failure Key ⊕ Unit) × Rand) :=
  match searchFrom pLen eB pB remaining s with
  | none => none
  | some (.error f, s) => some (.inl (.error f), s)
  | some (.ok c, s) =>
    some (keyFromPrimes (16 * pLen) (os2ip eB) (os2ip pB) (os2ip (i2osp c pLen)), s)

/-- The rest of an iteration of `rsa_generate_key_impl`'s loop (`keyStep`)
from the prime `phase` draws, with `remaining` rejected candidates left, on
the stream `s`. -/
def stepFrom (pLen : Nat) (eB : List Byte) : KeyPhase → Nat → Rand →
    Option ((Except Failure Key ⊕ Unit) × Rand)
  | .q pB, remaining, s => stepQ pLen eB pB remaining s
  | .p, remaining, s =>
    match searchFrom pLen eB [] remaining s with
    | none => none
    | some (.error f, s) => some (.inl (.error f), s)
    | some (.ok c, s) => stepQ pLen eB (i2osp c pLen) (primeLimit (8 * pLen) (os2ip eB)) s

/-- The rest of a generation (`generateOnce`) from the prime `phase` draws,
with `remaining` rejected candidates left, on the stream `s`. -/
def onceFrom (pLen : Nat) (eB : List Byte) (phase : KeyPhase) (remaining : Nat) (s : Rand) :
    Option (Except Failure Key × Rand) :=
  match stepFrom pLen eB phase remaining s with
  | none => none
  | some (.inl a, s) => some (a, s)
  | some (.inr (), s) => generateOnce (16 * pLen) (os2ip eB) s

/-- What is left of `generate` from the key search's state `st`, on the
stream `s`: the rest of this generation, and if it fails with too many tries,
`st.left - 1` more (`generate.attempts`). -/
def keyFrom (pLen : Nat) (eB : List Byte) (st : KeyProgress) (s : Rand) :
    Option (Except Failure Key) :=
  match onceFrom pLen eB st.phase st.remaining s with
  | none => none
  | some (.error .tooManyIterations, s) => generate.attempts (os2ip eB) (16 * pLen) (st.left - 1) s
  | some (.error f, _) => some (.error f)
  | some (.ok k, _) => some (.ok k)

/-- What a call of the key search from the state `st`, which returned `r`,
says of `keyFrom` on the stream `s` its tape starts. -/
def KeySearchAgrees (pLen : Nat) (eB : List Byte) (st : KeyProgress) (s : Rand)
    (r : KeySearchResult) : Prop :=
  match r.outcome with
  | .accepted k => keyFrom pLen eB st s = some k
  | .entropy st' _ => 0 < st'.remaining ∧ st'.remaining ≤ primeLimit (8 * pLen) (os2ip eB) ∧
      keyFrom pLen eB st s = keyFrom pLen eB st' (s.drop r.used)
  | .exhausted => keyFrom pLen eB st s = some (.error .tooManyIterations)

/-- The stream `s` holds, after some point, at least `primeEntropy pLen`
octets in which a candidate does not finish: where a search may run into its
budget. -/
def BudgetHit (pLen : Nat) (eB : List Byte) (s : Rand) : Prop :=
  ∃ pB u, u <:+ s ∧ primeEntropy pLen ≤ u.length ∧
    candidateOp pLen eB pB (u.take (primeEntropy pLen)) = none

/-! ## Loops and candidates -/

private theorem loop_inl {σ α : Type} {step : σ → Rand → Option ((α ⊕ σ) × Rand)}
    {P : α → Rand → Rand → Prop}
    (hs : ∀ s r a r', step s r = some (.inl a, r') → P a r r')
    (hmono : ∀ a r r₁ r', r₁.length < r.length → P a r₁ r' → P a r r')
    (s : σ) (r : Rand) (a : α) (r' : Rand) (h : loop step s r = some (a, r')) : P a r r' := by
  rw [loop] at h
  match hst : step s r with
  | none => rw [hst] at h; simp at h
  | some (.inl a', r₁) =>
    rw [hst] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hs s r _ _ hst
  | some (.inr s', r₁) =>
    rw [hst] at h
    simp only at h
    split at h
    · rename_i hlt
      exact hmono _ _ _ _ hlt (loop_inl hs hmono s' r₁ a r' h)
    · simp at h
termination_by r.length

private theorem candidate_lt {bits : Nat} (x : Nat) (hb : 2 ≤ bits) :
    candidate bits x < 2 ^ bits := by
  unfold candidate
  have h1 : x % 2 ^ bits < 2 ^ bits := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h2 : 3 * 2 ^ (bits - 2) < 2 ^ bits := by
    have : 2 ^ bits = 4 * 2 ^ (bits - 2) := by
      rw [show bits = bits - 2 + 2 by omega, Nat.pow_add]; simp only [Nat.add_sub_cancel]; omega
    have := Nat.two_pow_pos (bits - 2)
    omega
  have h3 : 1 < 2 ^ bits := Nat.one_lt_two_pow (by omega)
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow h1 h2) h3

private theorem candidateStep_prime {bits e : Nat} {p : Option Nat} {r r' : Rand} {c : Nat}
    (hb : 2 ≤ bits) (h : candidateStep bits e p r = some (.prime c, r')) : c < 2 ^ bits := by
  unfold candidateStep at h
  match hd : draw (bits / 8) r with
  | none => rw [hd] at h; simp at h
  | some (x, r1) =>
    rw [hd] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp [pure] at h
    · split at h
      · match hpt : primalityTest (candidate bits x) r1 with
        | none => rw [hpt] at h; simp at h
        | some (prime, r2) =>
          rw [hpt] at h
          simp only [Option.bind_some] at h
          split at h
          · simp only [pure, Option.some.injEq, Prod.mk.injEq, Candidate.prime.injEq] at h
            rw [← h.1]
            exact candidate_lt x hb
          · simp [pure] at h
      · simp [pure] at h

/-- A prime the search accepts on a stream has the primes' octets, and the
search read at least one octet for it. -/
private theorem searchFrom_ok {pLen : Nat} {eB pB : List Byte} {remaining : Nat} {s s' : Rand}
    {c : Nat} (hp : primeLenValid pLen)
    (h : searchFrom pLen eB pB remaining s = some (.ok c, s')) :
    c < 256 ^ pLen ∧ s'.length < s.length := by
  have hb : 2 ≤ 8 * pLen := by obtain ⟨h1, -⟩ := hp; omega
  have hb8 : 0 < 8 * pLen / 8 := by obtain ⟨h1, -⟩ := hp; omega
  have h256 : (256 : Nat) ^ pLen = 2 ^ (8 * pLen) := by rw [Nat.pow_mul]
  rw [h256]
  refine loop_inl (P := fun a r r' => ∀ c, a = .ok c → c < 2 ^ (8 * pLen) ∧ r'.length < r.length)
    ?_ ?_ _ s _ s' h c rfl
  · intro tries r a r' hst c hc
    subst hc
    unfold primeStep at hst
    match hcs : candidateStep (8 * pLen) (os2ip eB) (otherPrime pB) r with
    | none => rw [hcs] at hst; simp at hst
    | some (res, r₁) =>
      rw [hcs] at hst
      have hlen := (candidateStep_reads (t := []) hcs).2.2
      cases res with
      | prime c' =>
        simp only [Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq,
          Prod.mk.injEq, Sum.inl.injEq, Except.ok.injEq] at hst
        obtain ⟨rfl, rfl⟩ := hst
        exact ⟨candidateStep_prime hb hcs, by omega⟩
      | close => simp [pure] at hst
      | rejected =>
        simp only [Option.bind_eq_bind, Option.bind_some] at hst
        split at hst <;> simp [pure] at hst
  · intro a r r₁ r' hlt h c hc
    obtain ⟨h1, h2⟩ := h c hc
    exact ⟨h1, by omega⟩

private theorem os2ip_i2osp_mod (x k : Nat) : os2ip (i2osp x k) = x % 256 ^ k := by
  induction k generalizing x with
  | zero => simp [i2osp, os2ip, Nat.mod_one]
  | succ k ih =>
    have hs : i2osp x (k + 1) = i2osp (x / 256) k ++ [BitVec.ofNat 8 x] := by
      simp only [i2osp, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      congr 1
      · refine List.map_congr_left fun i hi => ?_
        have hi := List.mem_range.mp hi
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
        congr 3
        omega
      · rw [show k + 1 - 1 - k = 0 by omega, Nat.pow_zero, Nat.div_one]
    rw [hs, os2ip, List.foldl_append, List.foldl_cons, List.foldl_nil, ← os2ip, ih,
      Nat.pow_succ', Nat.mod_mul, BitVec.toNat_ofNat]
    omega

private theorem os2ip_i2osp_of_lt {x k : Nat} (hx : x < 256 ^ k) : os2ip (i2osp x k) = x := by
  rw [os2ip_i2osp_mod, Nat.mod_eq_of_lt hx]

private theorem otherPrime_i2osp {pLen c : Nat} (hp : 0 < pLen) (hc : c < 256 ^ pLen) :
    otherPrime (i2osp c pLen) = some c := by
  have hne : i2osp c pLen ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [i2osp] at this
    omega
  simp only [otherPrime, hne, ↓reduceIte, os2ip_i2osp_of_lt hc]

private theorem keyFromPrimes_ne (nlen e p q : Nat) :
    keyFromPrimes nlen e p q ≠ .inl (.error .tooManyIterations) := by
  intro h
  unfold keyFromPrimes at h
  generalize (if p < q then (q, p) else (p, q)) = pq at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h <;> simp at h

/-! ## From the start of a generation -/

/-- From `p`, with all its rejected candidates left, the rest of a
generation is `generateOnce`. -/
private theorem onceFrom_start {pLen : Nat} {eB : List Byte} (hp : primeLenValid pLen)
    (s : Rand) :
    onceFrom pLen eB .p (primeLimit (8 * pLen) (os2ip eB)) s =
      generateOnce (16 * pLen) (os2ip eB) s := by
  have hpos : 0 < pLen := by obtain ⟨h1, -⟩ := hp; omega
  have hhalf : 16 * pLen / 2 = 8 * pLen := by omega
  have hP0 : searchFrom pLen eB [] (primeLimit (8 * pLen) (os2ip eB)) s =
      generatePrime (8 * pLen) (os2ip eB) none s := by
    rw [searchFrom_init hp]; rfl
  rw [generateOnce, loop, onceFrom, stepFrom]
  simp only [keyStep, hhalf]
  rw [hP0]
  match hP : generatePrime (8 * pLen) (os2ip eB) none s with
  | none => rfl
  | some (.error f, s₁) => rfl
  | some (.ok c, s₁) =>
    have hP' : searchFrom pLen eB [] (primeLimit (8 * pLen) (os2ip eB)) s =
        some (.ok c, s₁) := by rw [hP0, hP]
    obtain ⟨hc, hl₁⟩ := searchFrom_ok hp hP'
    have hQ0 : searchFrom pLen eB (i2osp c pLen) (primeLimit (8 * pLen) (os2ip eB)) s₁ =
        generatePrime (8 * pLen) (os2ip eB) (some c) s₁ := by
      rw [searchFrom_init hp, otherPrime_i2osp hpos hc]
    simp only [Option.bind_eq_bind, Option.bind_some, stepQ]
    rw [hQ0]
    match hQ : generatePrime (8 * pLen) (os2ip eB) (some c) s₁ with
    | none => rfl
    | some (.error f, s₂) => rfl
    | some (.ok d, s₂) =>
      have hQ' : searchFrom pLen eB (i2osp c pLen) (primeLimit (8 * pLen) (os2ip eB)) s₁ =
          some (.ok d, s₂) := by rw [hQ0, hQ]
      obtain ⟨hd, hl₂⟩ := searchFrom_ok hp hQ'
      simp only [Option.bind_some, pure, os2ip_i2osp_of_lt hc, os2ip_i2osp_of_lt hd]
      generalize keyFromPrimes (16 * pLen) (os2ip eB) c d = k
      cases k with
      | inl a => rfl
      | inr u =>
        simp only
        rw [ite_eq_left (by omega)]
        rfl

/-- From `p`, with all its rejected candidates left and `k + 1` generations,
`keyFrom` is `k + 1` of `generate`'s generations. -/
private theorem keyFrom_start {pLen : Nat} {eB : List Byte} (hp : primeLenValid pLen)
    (k : Nat) (s : Rand) :
    keyFrom pLen eB ⟨k + 1, .p, primeLimit (8 * pLen) (os2ip eB)⟩ s =
      generate.attempts (os2ip eB) (16 * pLen) (k + 1) s := by
  rw [keyFrom, generate.attempts]
  simp only
  rw [onceFrom_start hp]
  rfl

/-! ## The search -/

private theorem keyFrom_congr {pLen : Nat} {eB : List Byte} {st : KeyProgress} {b : Nat}
    {s s' : Rand}
    (h : searchFrom pLen eB st.phase.other st.remaining s =
      searchFrom pLen eB st.phase.other b s') :
    keyFrom pLen eB st s = keyFrom pLen eB { st with remaining := b } s' := by
  obtain ⟨left, phase, remaining⟩ := st
  cases phase with
  | p => simp only [keyFrom, onceFrom, stepFrom, KeyPhase.other] at h ⊢; rw [h]
  | q pB => simp only [keyFrom, onceFrom, stepFrom, stepQ, KeyPhase.other] at h ⊢; rw [h]

private theorem keyAgrees_consume {pLen : Nat} {eB : List Byte} {st st' : KeyProgress}
    {s : Rand} {n : Nat} {prior : List Nat} {r : KeySearchResult}
    (heq : keyFrom pLen eB st s = keyFrom pLen eB st' (s.drop n))
    (h : KeySearchAgrees pLen eB st' (s.drop n) r) :
    KeySearchAgrees pLen eB st s (r.consume n prior) := by
  unfold KeySearchAgrees at h ⊢
  simp only [Entropy.Result.consume]
  split at h
  · rw [heq]; exact h
  · refine ⟨h.1, h.2.1, heq.trans ?_⟩
    rw [h.2.2, List.drop_drop]
  · rw [heq]; exact h

private theorem budgetHit_drop {pLen : Nat} {eB : List Byte} {s : Rand} {n : Nat}
    (h : BudgetHit pLen eB (s.drop n)) : BudgetHit pLen eB s := by
  obtain ⟨pB, u, hu, h1, h2⟩ := h
  exact ⟨pB, u, hu.trans (List.drop_suffix n s), h1, h2⟩

/-- **The key search is `generate`.** A call of `keySearch` for primes of a
valid length, from the state `st` with at least one rejected candidate left
(at most `primeLimit`), on the tape `rand`, agrees with `keyFrom` on every
stream `rand ++ t` (`KeySearchAgrees`), unless that stream holds a candidate
that does not finish within its search's budget (`BudgetHit`). -/
theorem keySearch_agrees {pLen : Nat} {eB : List Byte} (hp : primeLenValid pLen)
    (st : KeyProgress) (rand t : Rand) (h0 : 0 < st.remaining)
    (hl : st.remaining ≤ primeLimit (8 * pLen) (os2ip eB)) :
    KeySearchAgrees pLen eB st (rand ++ t) (keySearch pLen eB st rand) ∨
      BudgetHit pLen eB (rand ++ t) := by
  have hlim : 0 < primeLimit (8 * pLen) (os2ip eB) := by
    obtain ⟨h1, -⟩ := hp; unfold primeLimit; split <;> omega
  have hA := primeSearch_agrees (pB := st.phase.other) hp st.remaining rand t h0 hl
  have hle := primeSearch_used_le pLen eB st.phase.other st.remaining rand
  rw [keySearch]
  simp only
  generalize primeSearch pLen eB st.phase.other st.remaining rand = r at hA hle ⊢
  have hdrop : (rand ++ t).drop r.used = rand.drop r.used ++ t :=
    List.drop_append_of_le_length hle
  obtain ⟨outcome, used, trace⟩ := r
  simp only at hdrop hle
  cases outcome with
  | entropy remaining available =>
    left
    unfold SearchAgrees at hA
    obtain ⟨h1, h2, h3⟩ := hA
    exact ⟨h1, Nat.le_trans h2 hl, keyFrom_congr h3⟩
  | exhausted =>
    unfold SearchAgrees at hA
    simp only at hA
    rcases hA with hA | ⟨rem, -, -, hlen, hc⟩
    · have hk : keyFrom pLen eB st (rand ++ t) =
          generate.attempts (os2ip eB) (16 * pLen) (st.left - 1) ((rand ++ t).drop used) := by
        obtain ⟨left, phase, remaining⟩ := st
        cases phase with
        | p => simp only [keyFrom, onceFrom, stepFrom, KeyPhase.other] at hA ⊢; rw [hA]
        | q pB => simp only [keyFrom, onceFrom, stepFrom, stepQ, KeyPhase.other] at hA ⊢; rw [hA]
      simp only
      split
      · left
        unfold KeySearchAgrees
        simp only
        rw [hk, show st.left - 1 = 0 by omega, generate.attempts]
      · rename_i hleft
        have ih := keySearch_agrees hp ⟨st.left - 1, .p, primeLimit (8 * pLen) (os2ip eB)⟩
          (rand.drop used) t hlim (Nat.le_refl _)
        rw [← hdrop] at ih
        rcases ih with ih | ih
        · left
          refine keyAgrees_consume ?_ ih
          rw [hk, show st.left - 1 = st.left - 1 - 1 + 1 by omega, keyFrom_start hp]
        · exact Or.inr (budgetHit_drop ih)
    · exact Or.inr ⟨st.phase.other, _, List.drop_suffix used _, hlen, hc⟩
  | accepted c =>
    unfold SearchAgrees at hA
    simp only at hA
    have hlt := (searchFrom_ok hp hA).2
    have hpos : 0 < used := by
      rcases Nat.eq_zero_or_pos used with h | h
      · rw [h, List.drop_zero] at hlt; omega
      · exact h
    have hg : (rand.drop used).length < rand.length := by
      rw [List.length_drop]; omega
    simp only
    rw [dite_eq_left hg]
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      simp only
      have ih := keySearch_agrees hp ⟨left, .q (i2osp c pLen), primeLimit (8 * pLen) (os2ip eB)⟩
        (rand.drop used) t hlim (Nat.le_refl _)
      rw [← hdrop] at ih
      rcases ih with ih | ih
      · left
        refine keyAgrees_consume ?_ ih
        simp only [keyFrom, onceFrom, stepFrom, KeyPhase.other] at hA ⊢
        rw [hA]
      · exact Or.inr (budgetHit_drop ih)
    | q pB =>
      simp only
      have hstep : stepFrom pLen eB (.q pB) remaining (rand ++ t) =
          some (keyFromPrimes (16 * pLen) (os2ip eB) (os2ip pB) (os2ip (i2osp c pLen)),
            (rand ++ t).drop used) := by
        simp only [stepFrom, stepQ, KeyPhase.other] at hA ⊢
        rw [hA]
      have hne := keyFromPrimes_ne (16 * pLen) (os2ip eB) (os2ip pB) (os2ip (i2osp c pLen))
      generalize keyFromPrimes (16 * pLen) (os2ip eB) (os2ip pB) (os2ip (i2osp c pLen)) = k
        at hstep hne ⊢
      cases k with
      | inl res =>
        left
        unfold KeySearchAgrees
        simp only [keyFrom, onceFrom, hstep]
        cases res with
        | ok k => rfl
        | error f =>
          cases f with
          | tooManyIterations => exact absurd rfl hne
          | badParameters => rfl
          | internal => rfl
      | inr u =>
        have ih := keySearch_agrees hp ⟨left, .p, primeLimit (8 * pLen) (os2ip eB)⟩
          (rand.drop used) t hlim (Nat.le_refl _)
        rw [← hdrop] at ih
        rcases ih with ih | ih
        · left
          refine keyAgrees_consume ?_ ih
          simp only [keyFrom]
          rw [onceFrom_start hp]
          simp only [onceFrom, hstep]
        · exact Or.inr (budgetHit_drop ih)
termination_by (rand.length, st.left)
decreasing_by
  all_goals first
    | (rw [List.length_drop, Prod.lex_def]; omega)
    | exact Prod.Lex.left _ _ hg

/-! ## From the start -/

/-- **From `vg_rsa_generate_init`'s state, the key search is `generate`.**
For the size and the exponent's octets `eB` it accepts, `keyFrom`, for the
exponent's word it writes, from its state (`keyGenerations`, `p`, its
rejected candidates), is `generate` of the size and the exponent. -/
theorem keyFrom_init {bits limit pLen budget : Nat} {eB : List Byte}
    (h : keySearchInit bits eB = .ok [limit, pLen, budget]) (s : Rand) :
    primeLenValid pLen ∧ limit = primeLimit (8 * pLen) (os2ip (i2osp (os2ip eB) 8)) ∧
      keyFrom pLen (i2osp (os2ip eB) 8) ⟨keyGenerations, .p, limit⟩ s =
        generate bits (os2ip eB) s := by
  unfold keySearchInit at h
  simp only at h
  split at h
  · simp at h
  · rename_i hv
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hv
    split at h
    · simp at h
    · rename_i nlen hb
      simp only [Except.ok.injEq, List.cons.injEq, and_true] at h
      obtain ⟨rfl, rfl, -⟩ := h
      have he : os2ip (i2osp (os2ip eB) 8) = os2ip eB := by
        apply os2ip_i2osp_of_lt
        unfold exponentValid at hv
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
        omega
      have hn : 512 ≤ nlen ∧ nlen ≤ 8192 ∧ nlen % 128 = 0 := by
        unfold modulusBits at hb
        simp only [maxBits, minBits] at hb
        by_cases h1 : 8192 < bits
        · simp [h1] at hb
        · by_cases h2 : bits / 128 * 128 < 512
          · simp [h1, h2] at hb
          · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at hb
            omega
      have hp : primeLenValid (nlen / 16) := by unfold primeLenValid; omega
      refine ⟨hp, by rw [he], ?_⟩
      have hk := keyFrom_start (eB := i2osp (os2ip eB) 8) hp 3 s
      rw [he, show 16 * (nlen / 16) = nlen by omega] at hk
      rw [keyGenerations, hk, generate, params]
      simp only [hv, ↓reduceIte, hb]

end VG.Spec.RsaKeyGen
