module

-- separate module: names no ISA, so any target's scan of the tape can import it without x86's framework

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Random

/-!
# Drawing the padding string: the scan by its counts

The scan of `Proof/RsaPkcs1Enc/Random.lean` as the x86 code runs it, by the
octets kept and the octets left: before octet `j < scanLen n R` fewer than
`n` are kept (`nz_lt`); it stops after octet `j` exactly when `n` are kept
or the tape ends (`scan_stop_iff`); with `n` kept the padding string is the
octets kept (`prefix_full`), and otherwise the tape has fewer than `n`
nonzero octets (`nz_short`). The number kept after `j` octets is a function
of the trace (`cnt`, `nz_cnt`), and so is whether octet `j` is zero
(`zero_mask`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc

open VG.Spec.RsaPkcs1Enc

theorem nz_lt : ∀ {n j : Nat} {R : List Byte}, j < scanLen n R → (nz (R.take j)).length < n
  | 0, _, R, h => by cases R <;> simp [scanLen] at h
  | _ + 1, _, [], h => by simp [scanLen] at h
  | n + 1, 0, b :: R, _ => by simp [nz]
  | n + 1, j + 1, b :: R, h => by
    by_cases hb : b = 0
    · subst hb
      rw [scanLen, ite_eq_left rfl] at h
      rw [List.take_succ_cons, nz_cons_zero]
      exact nz_lt (by omega)
    · rw [scanLen, ite_eq_right hb] at h
      rw [List.take_succ_cons, nz_cons_ne hb, List.length_cons]
      have := nz_lt (n := n) (j := j) (R := R) (by omega)
      omega

theorem scanLen_end : ∀ (n : Nat) (R : List Byte),
    (nz (R.take (scanLen n R))).length = n ∨ scanLen n R = R.length
  | 0, R => by cases R <;> simp [scanLen, nz]
  | _ + 1, [] => by simp [scanLen]
  | n + 1, b :: R => by
    by_cases hb : b = 0
    · subst hb
      rw [scanLen, ite_eq_left rfl, List.take_succ_cons, nz_cons_zero, List.length_cons]
      rcases scanLen_end (n + 1) R with h | h
      · exact .inl h
      · exact .inr (by omega)
    · rw [scanLen, ite_eq_right hb, List.take_succ_cons, nz_cons_ne hb, List.length_cons, List.length_cons]
      rcases scanLen_end n R with h | h
      · exact .inl (by omega)
      · exact .inr (by omega)

theorem nz_take_mono {xs : List Byte} {i j : Nat} (h : i ≤ j) :
    (nz (xs.take i)).length ≤ (nz (xs.take j)).length := by
  have e := List.take_append_drop i (xs.take j)
  rw [List.take_take, Nat.min_eq_left h] at e
  rw [← e, nz_append, List.length_append]; omega

theorem scan_stop_iff {n j : Nat} {R : List Byte} (hj : j < scanLen n R) :
    j + 1 = scanLen n R ↔ ((nz (R.take (j + 1))).length = n ∨ j + 1 = R.length) := by
  have hle := scanLen_le n R
  constructor
  · intro h
    rcases scanLen_end n R with e | e
    · exact .inl (h ▸ e)
    · exact .inr (h.trans e)
  · rintro (e | e)
    · exact Classical.byContradiction fun hne => by
        have := nz_lt (n := n) (j := j + 1) (R := R) (by omega)
        omega
    · omega

/-- The octets a padding string's scan kept. -/
theorem prefix_ps : ∀ {n : Nat} {R : List Byte} {r : List Byte × Nat},
    nonzeroPrefix n R = some r → r.1 = nz (R.take r.2)
  | 0, R, r, h => by
    cases R <;> (simp only [nonzeroPrefix, Option.some.injEq] at h; subst h; rfl)
  | _ + 1, [], _, h => by simp [nonzeroPrefix] at h
  | m + 1, b :: R, r, h => by
    by_cases hb : b = 0
    · subst hb
      rw [nonzeroPrefix, ite_eq_left rfl] at h
      obtain ⟨r', hr, e⟩ := Option.map_eq_some_iff.mp h
      subst e
      simp only [List.take_succ_cons, nz_cons_zero]
      exact prefix_ps hr
    · rw [nonzeroPrefix, ite_eq_right hb] at h
      obtain ⟨r', hr, e⟩ := Option.map_eq_some_iff.mp h
      subst e
      simp only [List.take_succ_cons, nz_cons_ne hb]
      rw [prefix_ps hr]

theorem nz_take_le (xs : List Byte) (j : Nat) : (nz (xs.take j)).length ≤ (nz xs).length := by
  have := nz_take_mono (xs := xs) (i := j) (j := xs.length + j) (by omega)
  rwa [List.take_of_length_le (show xs.length ≤ xs.length + j by omega)] at this

theorem prefix_full {n : Nat} {R : List Byte} (h : (nz (R.take (scanLen n R))).length = n) :
    nonzeroPrefix n R = some (nz (R.take (scanLen n R)), scanLen n R) := by
  obtain ⟨r, hr⟩ := nonzeroPrefix_isSome (n := n) (rand := R) (by have := nz_take_le R (scanLen n R); omega)
  have hu := used_eq hr
  have hp := prefix_ps hr
  rw [hr, ← hu, ← hp]

theorem nz_short {n : Nat} {R : List Byte} (h : (nz (R.take (scanLen n R))).length < n) :
    (nz R).length < n := by
  rcases scanLen_end n R with e | e
  · omega
  · rwa [e, List.take_length] at h

/-! ## By the trace -/

/-- The nonzero octets among the first `j` of the scan, from its trace. -/
def cnt (M : List Nat) (j : Nat) : Nat := ((M.take j).filter (· == 0)).length

theorem nz_zeroMask : ∀ xs : List Byte, (nz xs).length = ((zeroMask xs).filter (· == 0)).length
  | [] => rfl
  | b :: xs => by
    by_cases hb : b = 0
    · subst hb; simp [zeroMask] at *; exact nz_zeroMask xs
    · rw [nz_cons_ne hb]
      simp only [zeroMask, List.map_cons, hb, ↓reduceIte, List.filter_cons, List.length_cons]
      have := nz_zeroMask xs
      simp only [zeroMask] at this
      simp [this]

theorem nz_cnt {n j : Nat} {R : List Byte} (hj : j ≤ scanLen n R) :
    (nz (R.take j)).length = cnt (padSearch n R).trace j := by
  rw [cnt, trace_eq, zeroMask, ← List.map_take, List.take_take, Nat.min_eq_left hj, nz_zeroMask]
  rfl

theorem trace_length (n : Nat) (R : List Byte) : (padSearch n R).trace.length = scanLen n R := by
  rw [trace_eq, zeroMask_length, List.length_take, Nat.min_eq_left (scanLen_le n R)]

theorem zero_mask {n j : Nat} {R : List Byte} (hj : j < scanLen n R) :
    (R.getD j 0 = 0 ↔ (padSearch n R).trace.getD j 0 = 1) := by
  have hl := scanLen_le n R
  rw [trace_eq, zeroMask]
  by_cases h : R[j]'(by omega) = 0 <;>
    simp [List.getD_eq_getElem?_getD, hj, List.getElem?_eq_getElem (show j < R.length by omega), h]

end VG.Proof.RsaPkcs1Enc
