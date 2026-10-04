import VerifiedGarbage.Proof.Blake2.Spec

/-!
# A BLAKE2 round on four columns at once, for any word size

As `Lanes.lean` for BLAKE2b: the work vector as four rows of four words
(`4k…4k+3` for `k < 4`); the four column `G`s of a round are `G` on each
column of the rows at once (`mixColsP`), with the message words of column
`q` (`x q`, `y q`); the four diagonal `G`s are the same after rows 0, 2 and
3 are rotated left by three, one and two places (`rotInP`; row 1 stays), so
that column `q` holds diagonal `(q + 3) mod 4`, rotated back after it
(`rotOutP`). This is how code keeping each row in one vector register
computes a round (`round_colsP`).
-/

namespace VG.Proof.Blake2

open VG.Spec.Blake2

variable {w : Nat} (P : Params w)

/-- Component `k` of the result of `mix`: `a`, `b`, `c` or `d`. -/
def pick4 (k : Nat) (x : BitVec w × BitVec w × BitVec w × BitVec w) : BitVec w :=
  match k with
  | 0 => x.1
  | 1 => x.2.1
  | 2 => x.2.2.1
  | _ => x.2.2.2

/-- `G` on each column `q` (words `q`, `4 + q`, `8 + q`, `12 + q`) at once,
with the message words `x q` and `y q`. -/
def mixColsP (x y : Nat → BitVec w) (v : Work w) : Work w :=
  Vector.ofFn fun j => pick4 (j.val / 4)
    (mix P (v[j.val % 4]'(by omega)) (v[4 + j.val % 4]'(by omega)) (v[8 + j.val % 4]'(by omega))
      (v[12 + j.val % 4]'(by omega)) (x (j.val % 4)) (y (j.val % 4)))

/-- Rows 0, 2 and 3 rotated left by three, one and two places. -/
def rotInP (v : Work w) : Work w :=
  Vector.ofFn fun j => v[4 * (j.val / 4) + (j.val % 4 + j.val / 4 + 3) % 4]'(by omega)

/-- Rows 0, 2 and 3 rotated left by one, three and two places (back). -/
def rotOutP (v : Work w) : Work w :=
  Vector.ofFn fun j => v[4 * (j.val / 4) + (j.val % 4 + 3 * (j.val / 4) + 1) % 4]'(by omega)

theorem mixColsP_get (x y : Nat → BitVec w) (v : Work w) (j : Nat) (hj : j < 16) :
    (mixColsP P x y v)[j] = pick4 (j / 4) (mix P (v[j % 4]'(by omega)) (v[4 + j % 4]'(by omega))
      (v[8 + j % 4]'(by omega)) (v[12 + j % 4]'(by omega)) (x (j % 4)) (y (j % 4))) := by
  simp only [mixColsP, Vector.getElem_ofFn]

theorem rotInP_get (v : Work w) (j : Nat) (hj : j < 16) :
    (rotInP v)[j] = v[4 * (j / 4) + (j % 4 + j / 4 + 3) % 4]'(by omega) := by
  simp only [rotInP, Vector.getElem_ofFn]

theorem rotOutP_get (v : Work w) (j : Nat) (hj : j < 16) :
    (rotOutP v)[j] = v[4 * (j / 4) + (j % 4 + 3 * (j / 4) + 1) % 4]'(by omega) := by
  simp only [rotOutP, Vector.getElem_ofFn]

theorem cases16' {j : Nat} (hj : j < 16) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
    j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by
  omega

/-- The value of a literal index. -/
theorem val_lit16 (k : Nat) : (no_index (OfNat.ofNat k : Fin 16)).val = k % 16 := rfl

theorem G_getP (v : Work w) {a c d e : Fin 16} (hab : a.1 ≠ c.1) (hac : a.1 ≠ d.1)
    (had : a.1 ≠ e.1) (hcd : c.1 ≠ d.1) (hce : c.1 ≠ e.1) (hde : d.1 ≠ e.1) (x y : BitVec w)
    (k : Nat) (hk : k < 16) :
    (G P v a c d e x y)[k] =
      if c.1 = k then (mix P v[a.1] v[c.1] v[d.1] v[e.1] x y).2.1
      else if d.1 = k then (mix P v[a.1] v[c.1] v[d.1] v[e.1] x y).2.2.1
      else if e.1 = k then (mix P v[a.1] v[c.1] v[d.1] v[e.1] x y).2.2.2
      else if a.1 = k then (mix P v[a.1] v[c.1] v[d.1] v[e.1] x y).1 else v[k] :=
  G_get P v hab hac had hcd hce hde x y k hk

/-- The four column `G`s of a round. -/
theorem columns_eqP (x y : Nat → BitVec w) (v : Work w) :
    G P (G P (G P (G P v 0 4 8 12 (x 0) (y 0)) 1 5 9 13 (x 1) (y 1)) 2 6 10 14 (x 2) (y 2))
      3 7 11 15 (x 3) (y 3) = mixColsP P x y v := by
  apply Vector.ext
  intro j hj
  simp only [mixColsP_get]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := cases16' hj
  all_goals
    simp (disch := decide) only [G_getP, val_lit16, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, pick4]

/-- The four diagonal `G`s of a round, with the message words `x i` and `y i`
of diagonal `i`. -/
theorem diagonals_eqP (x y : Nat → BitVec w) (v : Work w) :
    G P (G P (G P (G P v 0 5 10 15 (x 0) (y 0)) 1 6 11 12 (x 1) (y 1)) 2 7 8 13 (x 2) (y 2))
      3 4 9 14 (x 3) (y 3) =
      rotOutP (mixColsP P (fun q => x ((q + 3) % 4)) (fun q => y ((q + 3) % 4)) (rotInP v)) := by
  apply Vector.ext
  intro j hj
  simp only [rotOutP_get, rotInP_get, mixColsP_get]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := cases16' hj
  all_goals
    simp (disch := decide) only [G_getP, val_lit16, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceMul, Nat.reduceEqDiff, ↓reduceIte, pick4]

/-- Round `r` on four columns: the column `G`s, then the diagonal ones. -/
theorem round_colsP (m : Block w) (v : Work w) (r : Nat) :
    round P m v r =
      rotOutP (mixColsP P (fun q => m (sigmaAt r (8 + 2 * ((q + 3) % 4))))
        (fun q => m (sigmaAt r (9 + 2 * ((q + 3) % 4))))
        (rotInP (mixColsP P (fun q => m (sigmaAt r (2 * q))) (fun q => m (sigmaAt r (2 * q + 1))) v))) := by
  rw [← diagonals_eqP P (fun i => m (sigmaAt r (8 + 2 * i))) (fun i => m (sigmaAt r (9 + 2 * i))),
    ← columns_eqP]
  rfl

end VG.Proof.Blake2
