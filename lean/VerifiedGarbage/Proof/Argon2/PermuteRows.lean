import VerifiedGarbage.Proof.Argon2.Spec

/-!
# P on four columns at once

The sixteen words P permutes, as four rows of four (`4k…4k+3` for
`k < 4`): the four column GBs of P are GB on each column of the rows at once
(`mixColumns`), and the four diagonal GBs are the same after row `k` is
rotated left by `k` places (`rotRows 1`), rotated back after it
(`rotRows 3`). This is how code keeping each row in one vector register
(of four 64-bit lanes) computes P (`permute_lanes`).
-/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

/-- Component `k` of the result of `mix`. -/
def mixAt (k : Nat) (x : Word × Word × Word × Word) : Word :=
  match k with
  | 0 => x.1
  | 1 => x.2.1
  | 2 => x.2.2.1
  | _ => x.2.2.2

/-- GB on each column `q` (words `q`, `4 + q`, `8 + q`, `12 + q`) at once. -/
def mixColumns (v : Vector Word 16) : Vector Word 16 :=
  Vector.ofFn fun j => mixAt (j.val / 4)
    (mix (v[j.val % 4]'(by omega)) (v[4 + j.val % 4]'(by omega)) (v[8 + j.val % 4]'(by omega))
      (v[12 + j.val % 4]'(by omega)))

/-- Row `k` (words `4k…4k+3`) rotated left by `n · k` places. -/
def rotRows (n : Nat) (v : Vector Word 16) : Vector Word 16 :=
  Vector.ofFn fun j => v[4 * (j.val / 4) + (j.val % 4 + n * (j.val / 4)) % 4]'(by omega)

theorem mixColumns_get (v : Vector Word 16) (j : Nat) (hj : j < 16) :
    (mixColumns v)[j] = mixAt (j / 4) (mix (v[j % 4]'(by omega)) (v[4 + j % 4]'(by omega))
      (v[8 + j % 4]'(by omega)) (v[12 + j % 4]'(by omega))) := by
  simp only [mixColumns, Vector.getElem_ofFn]

theorem rotRows_get (n : Nat) (v : Vector Word 16) (j : Nat) (hj : j < 16) :
    (rotRows n v)[j] = v[4 * (j / 4) + (j % 4 + n * (j / 4)) % 4]'(by omega) := by
  simp only [rotRows, Vector.getElem_ofFn]

theorem GB_get' (v : Vector Word 16) {a b c d : Fin 16} (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1)
    (had : a.1 ≠ d.1) (hbc : b.1 ≠ c.1) (hbd : b.1 ≠ d.1) (hcd : c.1 ≠ d.1)
    (k : Nat) (hk : k < 16) :
    (GB v a b c d)[k] =
      if b.1 = k then (mix v[a.1] v[b.1] v[c.1] v[d.1]).2.1
      else if c.1 = k then (mix v[a.1] v[b.1] v[c.1] v[d.1]).2.2.1
      else if d.1 = k then (mix v[a.1] v[b.1] v[c.1] v[d.1]).2.2.2
      else if a.1 = k then (mix v[a.1] v[b.1] v[c.1] v[d.1]).1 else v[k] :=
  GB_get v hab hac had hbc hbd hcd k hk

theorem cases16 {j : Nat} (hj : j < 16) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
    j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by
  omega

/-- The value of a literal index. -/
theorem val_lit (k : Nat) : (no_index (OfNat.ofNat k : Fin 16)).val = k % 16 := rfl

/-- The four column GBs of P. -/
theorem columns_eq (v : Vector Word 16) :
    GB (GB (GB (GB v 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15 = mixColumns v := by
  apply Vector.ext
  intro j hj
  simp only [mixColumns_get]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := cases16 hj
  all_goals
    simp (disch := decide) only [GB_get', val_lit, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, mixAt]

/-- The four diagonal GBs of P. -/
theorem diagonals_eq (v : Vector Word 16) :
    GB (GB (GB (GB v 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14 =
      rotRows 3 (mixColumns (rotRows 1 v)) := by
  apply Vector.ext
  intro j hj
  simp only [rotRows_get, mixColumns_get]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := cases16 hj
  all_goals
    simp (disch := decide) only [GB_get', val_lit, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceMul, Nat.reduceEqDiff, ↓reduceIte, mixAt]

/-- P is two rounds of GB on the columns of the rows. -/
theorem permute_lanes (v : Vector Word 16) :
    permute v = rotRows 3 (mixColumns (rotRows 1 (mixColumns v))) := by
  rw [← diagonals_eq, ← columns_eq]
  rfl

end VG.Proof.Argon2
