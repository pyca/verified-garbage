module

public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random

/-!
# Drawing the padding string from a tape: the scan

`padSearch` (`Spec/RsaPkcs1Enc/Random.lean`) as the loop every
implementation runs: it reads the tape's octets in order, keeps each nonzero
one, and stops once it has kept `psLen` of them or the tape ends. After `i`
octets it has kept `nz (rand.take i)`. `scanLen` is the number of octets it
reads, and `padSearch`'s trace is which of them are zero (`trace_eq`), so two
runs with the same trace read the same number of octets, and each of them
is zero in one run exactly when it is in the other (`zero_iff`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc

open VG.Spec.RsaPkcs1Enc

/-- The nonzero octets of `xs`, in order. -/
def nz (xs : List Byte) : List Byte := xs.filter (· != 0)

theorem nz_nil : nz [] = [] := rfl

theorem nz_append (xs ys : List Byte) : nz (xs ++ ys) = nz xs ++ nz ys := List.filter_append ..

theorem nz_zero (xs : List Byte) : nz (xs ++ [0]) = nz xs := by
  simp [nz, List.filter_append]

theorem nz_cons_ne {b : Byte} (hb : b ≠ 0) (xs : List Byte) : nz (b :: xs) = b :: nz xs :=
  List.filter_cons_of_pos (bne_iff_ne.mpr hb)

theorem nz_cons_zero (xs : List Byte) : nz ((0 : Byte) :: xs) = nz xs := by simp [nz]

theorem nz_ne {b : Byte} (hb : b ≠ 0) (xs : List Byte) : nz (xs ++ [b]) = nz xs ++ [b] := by
  rw [nz_append, nz_cons_ne hb, nz_nil]

theorem nz_length_le (xs : List Byte) : (nz xs).length ≤ xs.length := List.length_filter_le ..

/-- The number of octets of `rand` the scan for `n` nonzero octets reads. -/
def scanLen : Nat → List Byte → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, b :: rand => if b = 0 then scanLen (n + 1) rand + 1 else scanLen n rand + 1

theorem scanLen_le : ∀ (n : Nat) (rand : List Byte), scanLen n rand ≤ rand.length
  | 0, _ => by simp [scanLen]
  | _ + 1, [] => by simp [scanLen]
  | n + 1, b :: rand => by
    unfold scanLen
    split
    · have := scanLen_le (n + 1) rand; simp only [List.length_cons]; omega
    · have := scanLen_le n rand; simp only [List.length_cons]; omega

/-- With fewer than `n` nonzero octets before it, the scan of `xs ++ ys`
reads all of `xs` and goes on in `ys` for the rest. -/
theorem nonzeroPrefix_append : ∀ {n : Nat} (xs ys : List Byte), (nz xs).length < n →
    nonzeroPrefix n (xs ++ ys) =
      (nonzeroPrefix (n - (nz xs).length) ys).map fun r => (nz xs ++ r.1, xs.length + r.2)
  | n, [], ys, _ => by
    simp only [List.nil_append, nz_nil, List.length_nil, Nat.sub_zero, List.nil_append, Nat.zero_add]
    cases nonzeroPrefix n ys <;> rfl
  | 0, _ :: _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, b :: xs, ys, h => by
    by_cases hb : b = 0
    · subst hb
      have e : nz ((0 : Byte) :: xs) = nz xs := nz_cons_zero xs
      rw [e] at h ⊢
      rw [List.cons_append, nonzeroPrefix, ite_eq_left rfl, nonzeroPrefix_append xs ys h, Option.map_map]
      simp only [List.length_cons]
      congr 1
      funext r
      simp only [Function.comp, Prod.mk.injEq, true_and]
      omega
    · have e : nz (b :: xs) = b :: nz xs := nz_cons_ne hb xs
      rw [e] at h ⊢
      simp only [List.length_cons] at h
      rw [List.cons_append, nonzeroPrefix, ite_eq_right hb, nonzeroPrefix_append xs ys (by omega),
        Option.map_map]
      simp only [List.length_cons, Nat.add_sub_add_right]
      congr 1
      funext r
      simp only [Function.comp, List.cons_append, Prod.mk.injEq, true_and]
      omega

theorem scanLen_append : ∀ {n : Nat} (xs ys : List Byte), (nz xs).length < n →
    scanLen n (xs ++ ys) = xs.length + scanLen (n - (nz xs).length) ys
  | n, [], ys, _ => by simp [nz_nil]
  | 0, _ :: _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, b :: xs, ys, h => by
    by_cases hb : b = 0
    · subst hb
      have e : nz ((0 : Byte) :: xs) = nz xs := nz_cons_zero xs
      rw [e] at h ⊢
      rw [List.cons_append, scanLen, ite_eq_left rfl, scanLen_append xs ys h]
      simp only [List.length_cons]; omega
    · have e : nz (b :: xs) = b :: nz xs := nz_cons_ne hb xs
      rw [e] at h ⊢
      simp only [List.length_cons] at h
      rw [List.cons_append, scanLen, ite_eq_right hb, scanLen_append xs ys (by omega)]
      simp only [List.length_cons, Nat.add_sub_add_right]; omega

/-- Fewer than `n` nonzero octets: no padding string, and the scan reads
them all. -/
theorem nonzeroPrefix_none {n : Nat} {xs : List Byte} (h : (nz xs).length < n) :
    nonzeroPrefix n xs = none := by
  have := nonzeroPrefix_append xs [] h
  rw [List.append_nil] at this
  rw [this]
  obtain ⟨m, hm⟩ : ∃ m, n - (nz xs).length = m + 1 := ⟨n - (nz xs).length - 1, by omega⟩
  rw [hm]; rfl

theorem scanLen_all {n : Nat} {xs : List Byte} (h : (nz xs).length < n) :
    scanLen n xs = xs.length := by
  have := scanLen_append xs [] h
  rw [List.append_nil] at this
  rw [this]
  obtain ⟨m, hm⟩ : ∃ m, n - (nz xs).length = m + 1 := ⟨n - (nz xs).length - 1, by omega⟩
  rw [hm]; rfl

/-- The `n`th nonzero octet `b` after `xs`: the padding string is `xs`'s
nonzero octets and `b`, and the scan stops after `b`. -/
theorem nonzeroPrefix_last {n : Nat} {xs : List Byte} {b : Byte} (ys : List Byte) (hb : b ≠ 0)
    (h : (nz xs).length + 1 = n) :
    nonzeroPrefix n (xs ++ b :: ys) = some (nz xs ++ [b], xs.length + 1) := by
  rw [nonzeroPrefix_append xs (b :: ys) (by omega), show n - (nz xs).length = 0 + 1 by omega]
  simp only [nonzeroPrefix, ite_eq_right hb, Option.map]

theorem scanLen_last {n : Nat} {xs : List Byte} {b : Byte} (ys : List Byte) (hb : b ≠ 0)
    (h : (nz xs).length + 1 = n) : scanLen n (xs ++ b :: ys) = xs.length + 1 := by
  rw [scanLen_append xs (b :: ys) (by omega), show n - (nz xs).length = 0 + 1 by omega]
  simp only [scanLen, ite_eq_right hb]

/-- The scan, still short of `n` nonzero octets and with octets left, reads
past `i`. -/
theorem lt_scanLen {n i : Nat} {rand : List Byte} (h : (nz (rand.take i)).length < n)
    (hi : i < rand.length) : i < scanLen n rand := by
  have e := scanLen_append (rand.take i) (rand.drop i) h
  rw [List.take_append_drop] at e
  rw [e, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  obtain ⟨m, hm⟩ : ∃ m, n - (nz (rand.take i)).length = m + 1 :=
    ⟨n - (nz (rand.take i)).length - 1, by omega⟩
  rw [hm]
  obtain ⟨b, ys, hd⟩ : ∃ b ys, rand.drop i = b :: ys := by
    cases hc : rand.drop i with
    | nil => rw [List.drop_eq_nil_iff] at hc; omega
    | cons b ys => exact ⟨b, ys, rfl⟩
  rw [hd, scanLen]
  split <;> omega

/-! ## The trace -/

/-- A padding string's scan reads up to its last octet. -/
theorem used_eq : ∀ {n : Nat} {rand : List Byte} {r : List Byte × Nat},
    nonzeroPrefix n rand = some r → r.2 = scanLen n rand
  | 0, rand, r, h => by
    cases rand <;> (simp only [nonzeroPrefix, Option.some.injEq] at h; subst h; rfl)
  | _ + 1, [], _, h => by simp [nonzeroPrefix] at h
  | m + 1, b :: rand, r, h => by
    by_cases hb : b = 0
    · rw [nonzeroPrefix, ite_eq_left hb] at h
      rw [scanLen, ite_eq_left hb]
      obtain ⟨r', hr, e⟩ := Option.map_eq_some_iff.mp h
      subst e; simp only; rw [used_eq hr]
    · rw [nonzeroPrefix, ite_eq_right hb] at h
      rw [scanLen, ite_eq_right hb]
      obtain ⟨r', hr, e⟩ := Option.map_eq_some_iff.mp h
      subst e; simp only; rw [used_eq hr]

/-- At least `n` nonzero octets: a padding string. -/
theorem nonzeroPrefix_isSome : ∀ {n : Nat} {rand : List Byte}, n ≤ (nz rand).length →
    ∃ r, nonzeroPrefix n rand = some r
  | 0, rand, _ => by cases rand <;> exact ⟨_, rfl⟩
  | _ + 1, [], h => by simp [nz] at h
  | m + 1, b :: rand, h => by
    by_cases hb : b = 0
    · have e : nz (b :: rand) = nz rand := hb ▸ nz_cons_zero rand
      rw [e] at h
      obtain ⟨r, hr⟩ := nonzeroPrefix_isSome h
      exact ⟨_, by rw [nonzeroPrefix, ite_eq_left hb, hr]; rfl⟩
    · have e : nz (b :: rand) = b :: nz rand := nz_cons_ne hb rand
      rw [e, List.length_cons] at h
      obtain ⟨r, hr⟩ := nonzeroPrefix_isSome (n := m) (rand := rand) (by omega)
      exact ⟨_, by rw [nonzeroPrefix, ite_eq_right hb, hr]; rfl⟩

theorem trace_eq (n : Nat) (rand : List Byte) :
    (padSearch n rand).trace = zeroMask (rand.take (scanLen n rand)) := by
  unfold padSearch
  split
  · rename_i ps used hp
    rw [← used_eq hp]
  · rename_i hn
    have : scanLen n rand = rand.length := by
      by_cases hl : (nz rand).length < n
      · exact scanLen_all hl
      · obtain ⟨r, hr⟩ := nonzeroPrefix_isSome (n := n) (rand := rand) (by omega)
        rw [hr] at hn; cases hn
    split <;> simp only [this, List.take_length]

theorem zeroMask_length (xs : List Byte) : (zeroMask xs).length = xs.length := List.length_map ..

/-- Two tapes with the same trace: the scans read the
same number of octets. -/
theorem scanLen_eq {n : Nat} {r₁ r₂ : List Byte}
    (h : (padSearch n r₁).trace = (padSearch n r₂).trace) : scanLen n r₁ = scanLen n r₂ := by
  have := congrArg List.length h
  rw [trace_eq, trace_eq, zeroMask_length, zeroMask_length, List.length_take, List.length_take,
    Nat.min_eq_left (scanLen_le n r₁), Nat.min_eq_left (scanLen_le n r₂)] at this
  exact this

/-- Two tapes with the same trace: each octet the scan
reads is zero in one exactly when it is in the other. -/
theorem zero_iff {n i : Nat} {r₁ r₂ : List Byte}
    (h : (padSearch n r₁).trace = (padSearch n r₂).trace) (hi : i < scanLen n r₁) :
    (r₁.getD i 0 = 0 ↔ r₂.getD i 0 = 0) := by
  have hs := scanLen_eq h
  rw [trace_eq, trace_eq, ← hs] at h
  have h1 := scanLen_le n r₁
  have h2 := scanLen_le n r₂
  have e := congrArg (fun l => l.getD i 0) h
  simp only [zeroMask, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
    ite_eq_left hi] at e
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at e
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), Option.getD_some,
    Option.getD_some]
  simp only [Option.map_some, Option.getD_some] at e
  constructor <;> intro hz
  · by_cases hn : r₂[i] = 0
    · exact hn
    · rw [ite_eq_left hz, ite_eq_right hn] at e; cases e
  · by_cases hn : r₁[i] = 0
    · exact hn
    · rw [ite_eq_right hn, ite_eq_left hz] at e; cases e

/-! ## The outcomes -/

theorem padSearch_accepted {n : Nat} {rand ps : List Byte} {i : Nat}
    (h : nonzeroPrefix n rand = some (ps, i)) :
    (padSearch n rand).outcome = .accepted ps ∧ (padSearch n rand).used = i := by
  simp only [padSearch, h]; exact ⟨trivial, trivial⟩

theorem padSearch_exhausted {n : Nat} {rand : List Byte} (h : (nz rand).length < n)
    (hl : padEntropy n ≤ rand.length) :
    (padSearch n rand).outcome = .exhausted ∧ (padSearch n rand).used = rand.length := by
  simp only [padSearch, nonzeroPrefix_none h, ite_eq_left hl]; exact ⟨trivial, trivial⟩

theorem padSearch_entropy {n : Nat} {rand : List Byte} (h : (nz rand).length < n)
    (hl : rand.length < padEntropy n) :
    (padSearch n rand).outcome = .entropy () rand.length ∧ (padSearch n rand).used = 0 := by
  simp only [padSearch, nonzeroPrefix_none h, ite_eq_right (Nat.not_le.mpr hl)]; exact ⟨trivial, trivial⟩

end VG.Proof.RsaPkcs1Enc
