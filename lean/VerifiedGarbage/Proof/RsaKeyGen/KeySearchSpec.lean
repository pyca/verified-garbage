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

end VG.Proof.RsaKeyGen.KeySearch
