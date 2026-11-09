module

public import VerifiedGarbage.Spec.RsaKeyGen.KeySearch

/-! # The key search, one prime's search at a time

`keySearch` unfolded once for each way its prime's search ends, for any
target's controller.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.KeySearch

open VG VG.Spec.RsaKeyGen
open VG.Spec.Rsa (os2ip i2osp)

variable {L : Nat} {eB : List Byte}

/-- A prime search's entry in the key search's trace. -/
abbrev primeEntry (r : PrimeSearchResult) : List Nat :=
  0 :: ([r.status, r.used, r.available] ++ r.trace).length :: ([r.status, r.used, r.available] ++ r.trace)

/-- The search for the state's prime, from `st`. -/
abbrev primeOf (L : Nat) (eB : List Byte) (st : KeyProgress) (rand : Rand) : PrimeSearchResult :=
  primeSearch L eB st.phase.other st.remaining rand

/-- The counted candidates each prime's search starts with. -/
abbrev limitOf (L : Nat) (eB : List Byte) : Nat := primeLimit (8 * L) (os2ip eB)

theorem ks_entropy {st : KeyProgress} {rand : Rand} {k a : Nat}
    (h : (primeOf L eB st rand).outcome = .entropy k a) :
    keySearch L eB st rand =
      ⟨.entropy { st with remaining := k } a, (primeOf L eB st rand).used, primeEntry (primeOf L eB st rand)⟩ := by
  rw [keySearch]
  simp only [h]

theorem ks_exhausted_last {st : KeyProgress} {rand : Rand}
    (h : (primeOf L eB st rand).outcome = .exhausted) (hl : st.left ≤ 1) :
    keySearch L eB st rand = ⟨.exhausted, (primeOf L eB st rand).used, primeEntry (primeOf L eB st rand)⟩ := by
  rw [keySearch]
  simp only [h, hl, ↓reduceIte]

theorem ks_exhausted_next {st : KeyProgress} {rand : Rand}
    (h : (primeOf L eB st rand).outcome = .exhausted) (hl : ¬st.left ≤ 1) :
    keySearch L eB st rand =
      (keySearch L eB ⟨st.left - 1, .p, limitOf L eB⟩ (rand.drop (primeOf L eB st rand).used)).consume
        (primeOf L eB st rand).used (primeEntry (primeOf L eB st rand)) := by
  rw [keySearch]
  simp only [h, hl, ↓reduceIte]

theorem ks_accepted_none {st : KeyProgress} {rand : Rand} {c : Nat}
    (h : (primeOf L eB st rand).outcome = .accepted c)
    (hg : ¬(rand.drop (primeOf L eB st rand).used).length < rand.length) :
    keySearch L eB st rand = ⟨.exhausted, (primeOf L eB st rand).used, primeEntry (primeOf L eB st rand)⟩ := by
  rw [keySearch]
  simp only [h, hg, ↓reduceDIte]

theorem ks_accepted_p {st : KeyProgress} {rand : Rand} {c : Nat}
    (h : (primeOf L eB st rand).outcome = .accepted c)
    (hg : (rand.drop (primeOf L eB st rand).used).length < rand.length) (hp : st.phase = .p) :
    keySearch L eB st rand =
      (keySearch L eB ⟨st.left, .q (i2osp c L), limitOf L eB⟩ (rand.drop (primeOf L eB st rand).used)).consume
        (primeOf L eB st rand).used (primeEntry (primeOf L eB st rand)) := by
  obtain ⟨left, phase, remaining⟩ := st
  simp only at hp
  subst hp
  rw [keySearch]
  simp only [h, hg, ↓reduceDIte]

theorem ks_accepted_key {st : KeyProgress} {rand : Rand} {c : Nat} {pB : List Byte}
    {res : Except Failure Key}
    (h : (primeOf L eB st rand).outcome = .accepted c)
    (hg : (rand.drop (primeOf L eB st rand).used).length < rand.length) (hp : st.phase = .q pB)
    (hk : keyFromPrimes (16 * L) (os2ip eB) (os2ip pB) (os2ip (i2osp c L)) = .inl res) :
    keySearch L eB st rand =
      ⟨.accepted res, (primeOf L eB st rand).used,
        primeEntry (primeOf L eB st rand) ++ [1, keyResultStatus (.inl res)]⟩ := by
  obtain ⟨left, phase, remaining⟩ := st
  simp only at hp
  subst hp
  rw [keySearch]
  simp only [h, hg, ↓reduceDIte, hk]

theorem ks_accepted_small {st : KeyProgress} {rand : Rand} {c : Nat} {pB : List Byte}
    (h : (primeOf L eB st rand).outcome = .accepted c)
    (hg : (rand.drop (primeOf L eB st rand).used).length < rand.length) (hp : st.phase = .q pB)
    (hk : keyFromPrimes (16 * L) (os2ip eB) (os2ip pB) (os2ip (i2osp c L)) = .inr ()) :
    keySearch L eB st rand =
      (keySearch L eB ⟨st.left, .p, limitOf L eB⟩ (rand.drop (primeOf L eB st rand).used)).consume
        (primeOf L eB st rand).used (primeEntry (primeOf L eB st rand) ++ [1, 2]) := by
  obtain ⟨left, phase, remaining⟩ := st
  simp only at hp
  subst hp
  rw [keySearch]
  simp only [h, hg, ↓reduceDIte, hk]
  rfl

theorem consume_consume (r : KeySearchResult) (a b : Nat) (x y : List Nat) :
    (r.consume b y).consume a x = r.consume (a + b) (x ++ y) := by
  simp only [Spec.Entropy.Result.consume, Nat.add_assoc, List.append_assoc]

theorem consume_zero (r : KeySearchResult) : r.consume 0 [] = r := by
  cases r; simp [Spec.Entropy.Result.consume]

/-- A prime search never ends with more counted candidates than it started with. -/
theorem primeSearch_remaining_le (L : Nat) (eB pB : List Byte) (remaining : Nat) (rand : Rand) :
    (primeSearch L eB pB remaining rand).remaining ≤ remaining := by
  rw [primeSearch]
  split
  · exact Nat.zero_le _
  · simp only
    split
    · split
      · exact Nat.zero_le _
      · exact Nat.le_refl _
    · exact Nat.zero_le _
    · split
      · exact primeSearch_remaining_le L eB pB remaining _
      · exact Nat.zero_le _
    · split
      · rename_i rest _ _
        have := primeSearch_remaining_le L eB pB (remaining - 1) rest
        exact Nat.le_trans this (Nat.sub_le _ _)
      · exact Nat.zero_le _
termination_by rand.length

/-- A key search's trace starts with its prime search's entry. -/
theorem keySearch_trace (st : KeyProgress) (rand : Rand) :
    ∃ rest, (keySearch L eB st rand).trace = primeEntry (primeOf L eB st rand) ++ rest := by
  cases ho : (primeOf L eB st rand).outcome with
  | entropy k a => exact ⟨[], by rw [ks_entropy ho, List.append_nil]⟩
  | exhausted =>
    by_cases hl : st.left ≤ 1
    · exact ⟨[], by rw [ks_exhausted_last ho hl, List.append_nil]⟩
    · rw [ks_exhausted_next ho hl]
      exact ⟨_, rfl⟩
  | accepted c =>
    by_cases hg : (rand.drop (primeOf L eB st rand).used).length < rand.length
    · obtain ⟨left, phase, remaining⟩ := st
      cases phase with
      | p =>
        rw [ks_accepted_p ho hg rfl]
        exact ⟨_, rfl⟩
      | q pB =>
        cases hk : keyFromPrimes (16 * L) (os2ip eB) (os2ip pB) (os2ip (i2osp c L)) with
        | inl res => exact ⟨[1, keyResultStatus (.inl res)], by rw [ks_accepted_key ho hg rfl hk]⟩
        | inr u =>
          rw [ks_accepted_small ho hg rfl hk]
          exact ⟨[1, 2] ++ (keySearch L eB ⟨left, .p, limitOf L eB⟩
            (rand.drop (primeOf L eB ⟨left, .q pB, remaining⟩ rand).used)).trace, by
              simp only [Spec.Entropy.Result.consume, List.append_assoc]⟩
    · exact ⟨[], by rw [ks_accepted_none ho hg, List.append_nil]⟩

/-- After `q`'s search accepted a prime, the key's status follows its entry. -/
theorem keySearch_trace_key {st : KeyProgress} {rand : Rand} {c : Nat} {pB : List Byte}
    (h : (primeOf L eB st rand).outcome = .accepted c)
    (hg : (rand.drop (primeOf L eB st rand).used).length < rand.length) (hp : st.phase = .q pB) :
    ∃ rest, (keySearch L eB st rand).trace = primeEntry (primeOf L eB st rand) ++
      [1, keyResultStatus (keyFromPrimes (16 * L) (os2ip eB) (os2ip pB) (os2ip (i2osp c L)))] ++ rest := by
  cases hk : keyFromPrimes (16 * L) (os2ip eB) (os2ip pB) (os2ip (i2osp c L)) with
  | inl res => exact ⟨[], by rw [ks_accepted_key h hg hp hk, List.append_nil]⟩
  | inr u =>
    rw [ks_accepted_small h hg hp hk]
    exact ⟨_, by simp only [Spec.Entropy.Result.consume, List.append_assoc]; rfl⟩

/-! ## What a trace says of its first step -/

/-- The first step's prime search: its status, consumption and octets left. -/
abbrev traceStatus (tr : List Nat) : Nat := tr.getD 2 0
abbrev traceUsed (tr : List Nat) : Nat := tr.getD 3 0
abbrev traceAvailable (tr : List Nat) : Nat := tr.getD 4 0
/-- The prime search's entry's length. -/
abbrev traceEntry (tr : List Nat) : Nat := tr.getD 1 0 + 2
/-- The prime search's own trace. -/
abbrev tracePrime (tr : List Nat) : List Nat := (tr.drop 5).take (tr.getD 1 0 - 3)
/-- The key's status after the prime search's entry. -/
abbrev traceKey (tr : List Nat) : Nat := tr.getD (traceEntry tr + 1) 0

theorem primeEntry_facts (r : PrimeSearchResult) (rest : List Nat) :
    traceStatus (primeEntry r ++ rest) = r.status ∧ traceUsed (primeEntry r ++ rest) = r.used ∧
      traceAvailable (primeEntry r ++ rest) = r.available ∧
      tracePrime (primeEntry r ++ rest) = r.trace ∧
      traceEntry (primeEntry r ++ rest) = (primeEntry r).length := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · simp [primeEntry, tracePrime]
  · simp [primeEntry]

theorem primeEntry_key (r : PrimeSearchResult) (k : Nat) (rest : List Nat) :
    traceKey (primeEntry r ++ [1, k] ++ rest) = k := by
  simp only [traceKey, traceEntry, primeEntry, List.cons_append, List.append_assoc]
  simp [List.getD_eq_getElem?_getD]

end VG.Proof.RsaKeyGen.KeySearch
