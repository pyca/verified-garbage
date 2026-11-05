module

public import VerifiedGarbage.Spec.Ffdh.SievedGeneration

/-! # What the sieved FFDH parameter search accepts

**Trusted statement, proven here.** The contract of
`vg_ffdh_generate_parameters` (`SievedContract.lean`) is exact about the tape,
so it fixes a search policy that no standard defines: RSA's trial division
before the Miller–Rabin rounds, the order the witnesses of p and q are drawn
in, the attempt bound and the entropy requests. `sievedParameterSearch_accepted`
says that none of that changes what an accepted p satisfies: the plain test,
`generateParameters` (`Ffdh.lean`), accepts p with its `primeChecks` witnesses
for p and for q = (p - 1) / 2. The candidate is the plain one, `candidateOf`
the octets that start a suffix of the tape, and each witness is drawn by the
plain rejection sampler, `drawWitness` (`drawWitnesses` draws with it), from
the octets after the previous one: one witness of p, all of q's, then p's
others. So p = 2q + 1 has `bits` bits and the generator's congruence, and p
and q are probable primes by the independent witness counts of `Ffdh.lean`:
the sieve and the policy can only reject more candidates, never accept one
the plain test rejects.
-/

@[expose] public section
namespace VG.Spec.Ffdh
open VG.Spec.RsaKeyGen (Rand draw loop bitLength)

private theorem draw_suffix {len : Nat} {r rest : Rand} {x : Nat}
    (h : draw len r = some (x, rest)) : rest <:+ r := by
  unfold draw at h
  dsimp only at h
  split at h
  · cases h
    exact List.drop_suffix _ _
  · cases h

private theorem loop_suffix {σ α : Type} {step : σ → Rand → Option ((α ⊕ σ) × Rand)}
    (hstep : ∀ s r y rest, step s r = some (y, rest) → rest <:+ r) :
    ∀ n (s : σ) (r : Rand) (a : α) (rest : Rand), r.length < n →
      loop step s r = some (a, rest) → rest <:+ r := by
  intro n
  induction n with
  | zero => intro _ _ _ _ hn; omega
  | succ n ih =>
    intro s r a rest hn h
    rw [loop] at h
    split at h
    · cases h
    · rename_i a' r' hs
      cases h
      exact hstep _ _ _ _ hs
    · rename_i s' r' hs
      split at h
      · rename_i hlt
        exact (ih s' r' a rest (by omega) h).trans (hstep _ _ _ _ hs)
      · cases h

private theorem drawWitness_suffix {w a : Nat} {r rest : Rand}
    (h : drawWitness w r = some (a, rest)) : rest <:+ r := by
  refine loop_suffix ?_ (r.length + 1) () r a rest (Nat.lt_succ_self _) h
  intro _ r y rest hs
  unfold witnessStep at hs
  cases hd : draw (witnessOctets w) r with
  | none => simp only [hd, bind, Option.bind_none, reduceCtorEq] at hs
  | some xr =>
    obtain ⟨x, r'⟩ := xr
    simp only [hd, bind, Option.bind_some, pure] at hs
    split at hs <;>
    · cases hs
      exact draw_suffix hd

private theorem drawWitnesses_suffix {w : Nat} :
    ∀ n (r : Rand) (as : List Nat) (rest : Rand), drawWitnesses w n r = some (as, rest) →
      rest <:+ r := by
  intro n
  induction n with
  | zero =>
    intro r as rest h
    cases h
    exact List.suffix_refl _
  | succ n ih =>
    intro r as rest h
    unfold drawWitnesses at h
    cases hd : drawWitness w r with
    | none => simp only [hd, bind, Option.bind_none, reduceCtorEq] at h
    | some ar =>
      obtain ⟨a, r'⟩ := ar
      simp only [hd, bind, Option.bind_some] at h
      split at h
      · cases hn : drawWitnesses w n r' with
        | none => simp only [hn, Option.bind_none, reduceCtorEq] at h
        | some asr =>
          obtain ⟨as', r''⟩ := asr
          simp only [hn, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
          exact h.2 ▸ (ih _ _ _ hn).trans (drawWitness_suffix hd)
      · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        exact h.2 ▸ drawWitness_suffix hd

private theorem screened_suffix {p q : Nat} {r rest : Rand} {pass : Bool}
    (h : screenedParameterWitnesses p q r = some (pass, rest)) : rest <:+ r := by
  unfold screenedParameterWitnesses at h
  cases h₁ : drawWitness p r with
  | none => simp only [h₁, bind, Option.bind_none, reduceCtorEq] at h
  | some ar =>
    obtain ⟨a, r₁⟩ := ar
    have s₁ := drawWitness_suffix h₁
    simp only [h₁, bind, Option.bind_some] at h
    split at h
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2 ▸ s₁
    · cases h₂ : drawWitnesses q (primeChecks (bitLength q)) r₁ with
      | none => simp only [h₂, Option.bind_none, reduceCtorEq] at h
      | some wr =>
        obtain ⟨wq, r₂⟩ := wr
        have s₂ := (drawWitnesses_suffix _ _ _ _ h₂).trans s₁
        simp only [h₂, Option.bind_some] at h
        split at h
        · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
          exact h.2 ▸ s₂
        · cases h₃ : drawWitnesses p (primeChecks (bitLength p) - 1) r₂ with
          | none => simp only [h₃, Option.bind_none, reduceCtorEq] at h
          | some wr =>
            obtain ⟨wp, r₃⟩ := wr
            simp only [h₃, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
            exact h.2 ▸ (drawWitnesses_suffix _ _ _ _ h₃).trans s₂

private theorem candidate_suffix {bits generator : Nat} {r rest : Rand} {v : Option Nat}
    (h : sievedParameterCandidate bits generator r = some (v, rest)) : rest <:+ r := by
  unfold sievedParameterCandidate at h
  cases hd : draw ((bits + 7) / 8) r with
  | none => simp only [hd, bind, Option.bind_none, reduceCtorEq] at h
  | some xr =>
    obtain ⟨x, r₀⟩ := xr
    have s₀ := draw_suffix hd
    simp only [hd, bind, Option.bind_some] at h
    split at h
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2 ▸ s₀
    · cases hs : screenedParameterWitnesses (candidateOf bits x) ((candidateOf bits x - 1) / 2) r₀ with
      | none => simp only [hs, Option.bind_none, reduceCtorEq] at h
      | some pr =>
        obtain ⟨pass, r₁⟩ := pr
        simp only [hs, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
        exact h.2 ▸ (screened_suffix hs).trans s₀

/-- An accepted candidate: the plain candidate, its witnesses drawn one after
another from the rest of the tape, and the plain test's acceptance. -/
theorem sievedParameterCandidate_accepted {bits generator p : Nat} {r rest : Rand}
    (h : sievedParameterCandidate bits generator r = some (some p, rest)) :
    ∃ x t₀ a t₁ wq t₂ wp,
      draw ((bits + 7) / 8) r = some (x, t₀) ∧ p = candidateOf bits x ∧
      drawWitness p t₀ = some (a, t₁) ∧
      drawWitnesses ((p - 1) / 2) (primeChecks (bitLength ((p - 1) / 2))) t₁ = some (wq, t₂) ∧
      drawWitnesses p (primeChecks (bitLength p) - 1) t₂ = some (wp, rest) ∧
      generateParameters bits generator [(p, a :: wp, wq)] = some ⟨p, generator, none⟩ := by
  unfold sievedParameterCandidate at h
  cases hd : draw ((bits + 7) / 8) r with
  | none => simp only [hd, bind, Option.bind_none, reduceCtorEq] at h
  | some xr =>
    obtain ⟨x, t₀⟩ := xr
    simp only [hd, bind, Option.bind_some] at h
    split at h
    · simp only [pure, Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at h
    · rename_i hc
      have shape : generationShape bits generator (candidateOf bits x) = true := by
        revert hc
        cases generationShape bits generator (candidateOf bits x) <;> simp
      cases hs : screenedParameterWitnesses (candidateOf bits x) ((candidateOf bits x - 1) / 2) t₀ with
      | none => simp only [hs, Option.bind_none, reduceCtorEq] at h
      | some pr =>
        obtain ⟨pass, t'⟩ := pr
        simp only [hs, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hp, rfl⟩ := h
        cases pass with
        | false => simp only [Bool.false_eq_true, ite_false, reduceCtorEq] at hp
        | true =>
          simp only [ite_true, Option.some.injEq] at hp
          subst hp
          unfold screenedParameterWitnesses at hs
          cases h₁ : drawWitness (candidateOf bits x) t₀ with
          | none => simp only [h₁, bind, Option.bind_none, reduceCtorEq] at hs
          | some ar =>
            obtain ⟨a, t₁⟩ := ar
            simp only [h₁, bind, Option.bind_some] at hs
            split at hs
            · simp only [pure, Option.some.injEq, Prod.mk.injEq, Bool.false_eq_true,
                false_and] at hs
            · cases h₂ : drawWitnesses ((candidateOf bits x - 1) / 2)
                  (primeChecks (bitLength ((candidateOf bits x - 1) / 2))) t₁ with
              | none => simp only [h₂, Option.bind_none, reduceCtorEq] at hs
              | some wr =>
                obtain ⟨wq, t₂⟩ := wr
                simp only [h₂, Option.bind_some] at hs
                split at hs
                · simp only [pure, Option.some.injEq, Prod.mk.injEq, Bool.false_eq_true,
                    false_and] at hs
                · rename_i hq
                  cases h₃ : drawWitnesses (candidateOf bits x)
                      (primeChecks (bitLength (candidateOf bits x)) - 1) t₂ with
                  | none => simp only [h₃, Option.bind_none, reduceCtorEq] at hs
                  | some wr =>
                    obtain ⟨wp, t₃⟩ := wr
                    simp only [h₃, Option.bind_some, pure, Option.some.injEq,
                      Prod.mk.injEq] at hs
                    obtain ⟨hpp, rfl⟩ := hs
                    refine ⟨x, t₀, a, t₁, wq, t₂, wp, rfl, rfl, h₁, h₂, h₃, ?_⟩
                    have hq' : probablePrime ((candidateOf bits x - 1) / 2) wq = true := by
                      revert hq
                      cases probablePrime ((candidateOf bits x - 1) / 2) wq <;> simp
                    simp only [generateParameters, shape, hpp, hq', Bool.and_self, ite_true]

private theorem consume_accepted {n p used : Nat} {res : ParameterSearchResult}
    (h : res.consume n = .accepted p used) : ∃ u, res = .accepted p u := by
  cases res <;> simp only [ParameterSearchResult.consume, ParameterSearchResult.accepted.injEq,
    reduceCtorEq] at h
  exact ⟨_, by rw [h.1]⟩

private theorem search_accepted {bits generator p : Nat} :
    ∀ (remaining : Nat) (r : Rand) (used : Nat),
      sievedParameterSearch bits generator remaining r = .accepted p used →
      ∃ t rest, t <:+ r ∧ sievedParameterCandidate bits generator t = some (some p, rest) := by
  intro remaining
  induction remaining with
  | zero => intro r used h; simp only [sievedParameterSearch, reduceCtorEq] at h
  | succ n ih =>
    intro r used h
    unfold sievedParameterSearch at h
    split at h
    · split at h <;> simp only [reduceCtorEq] at h
    · rename_i p' rest hc
      simp only [ParameterSearchResult.accepted.injEq] at h
      exact ⟨r, rest, List.suffix_refl _, h.1 ▸ hc⟩
    · rename_i rest hc
      obtain ⟨u, hu⟩ := consume_accepted h
      obtain ⟨t, rest', ht, hcand⟩ := ih rest u hu
      exact ⟨t, rest', ht.trans (candidate_suffix hc), hcand⟩

/-- An accepted p of the sieved search (the contract's `.accepted`) is one the
plain test `generateParameters` accepts, with the candidate taken from a
suffix of the tape and its witnesses drawn by `drawWitness` from the octets
after it, one after another: one of p, all of q's, then p's others. -/
theorem sievedParameterSearch_accepted {bits generator remaining p used : Nat} {r : Rand}
    (h : sievedParameterSearch bits generator remaining r = .accepted p used) :
    ∃ t x t₀ a t₁ wq t₂ wp rest, t <:+ r ∧
      draw ((bits + 7) / 8) t = some (x, t₀) ∧ p = candidateOf bits x ∧
      drawWitness p t₀ = some (a, t₁) ∧
      drawWitnesses ((p - 1) / 2) (primeChecks (bitLength ((p - 1) / 2))) t₁ = some (wq, t₂) ∧
      drawWitnesses p (primeChecks (bitLength p) - 1) t₂ = some (wp, rest) ∧
      generateParameters bits generator [(p, a :: wp, wq)] = some ⟨p, generator, none⟩ := by
  obtain ⟨t, rest, ht, hc⟩ := search_accepted remaining r used h
  obtain ⟨x, t₀, a, t₁, wq, t₂, wp, hd, hp, h₁, h₂, h₃, hg⟩ :=
    sievedParameterCandidate_accepted hc
  exact ⟨t, x, t₀, a, t₁, wq, t₂, wp, rest, ht, hd, hp, h₁, h₂, h₃, hg⟩

end VG.Spec.Ffdh
