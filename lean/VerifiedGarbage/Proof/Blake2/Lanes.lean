import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Proof.Argon2.PermuteRows

/-!
# A BLAKE2b round on four columns at once

The work vector as four rows of four words (`4k…4k+3` for `k < 4`): the four
column `G`s of a round are `G` on each column of the rows at once
(`mixCols`), with the message words of column `q` (`x q`, `y q`). The four
diagonal `G`s are the same after rows 0, 2 and 3 are rotated left by three,
one and two places (`rotIn`; row 1 stays), so that column `q` holds diagonal
`(q + 3) mod 4`, rotated back after it (`rotOut`). This is how code keeping
each row in one vector register (of four 64-bit lanes) computes a round
(`round_lanes`).
-/

namespace VG.Proof.Blake2

open VG.Spec.Blake2
open VG.Proof.Argon2 (mixAt cases16 val_lit)

/-- `G` on each column `q` (words `q`, `4 + q`, `8 + q`, `12 + q`) at once,
with the message words `x q` and `y q`. -/
def mixCols (x y : Nat → BitVec 64) (v : Work 64) : Work 64 :=
  Vector.ofFn fun j => mixAt (j.val / 4)
    (mix b (v[j.val % 4]'(by omega)) (v[4 + j.val % 4]'(by omega)) (v[8 + j.val % 4]'(by omega))
      (v[12 + j.val % 4]'(by omega)) (x (j.val % 4)) (y (j.val % 4)))

/-- Rows 0, 2 and 3 rotated left by three, one and two places. -/
def rotIn (v : Work 64) : Work 64 :=
  Vector.ofFn fun j => v[4 * (j.val / 4) + (j.val % 4 + j.val / 4 + 3) % 4]'(by omega)

/-- Rows 0, 2 and 3 rotated left by one, three and two places (back). -/
def rotOut (v : Work 64) : Work 64 :=
  Vector.ofFn fun j => v[4 * (j.val / 4) + (j.val % 4 + 3 * (j.val / 4) + 1) % 4]'(by omega)

theorem mixCols_get (x y : Nat → BitVec 64) (v : Work 64) (j : Nat) (hj : j < 16) :
    (mixCols x y v)[j] = mixAt (j / 4) (mix b (v[j % 4]'(by omega)) (v[4 + j % 4]'(by omega))
      (v[8 + j % 4]'(by omega)) (v[12 + j % 4]'(by omega)) (x (j % 4)) (y (j % 4))) := by
  simp only [mixCols, Vector.getElem_ofFn]

theorem rotIn_get (v : Work 64) (j : Nat) (hj : j < 16) :
    (rotIn v)[j] = v[4 * (j / 4) + (j % 4 + j / 4 + 3) % 4]'(by omega) := by
  simp only [rotIn, Vector.getElem_ofFn]

theorem rotOut_get (v : Work 64) (j : Nat) (hj : j < 16) :
    (rotOut v)[j] = v[4 * (j / 4) + (j % 4 + 3 * (j / 4) + 1) % 4]'(by omega) := by
  simp only [rotOut, Vector.getElem_ofFn]

theorem G_get' (v : Work 64) {a c d e : Fin 16} (hab : a.1 ≠ c.1) (hac : a.1 ≠ d.1)
    (had : a.1 ≠ e.1) (hbc : c.1 ≠ d.1) (hbd : c.1 ≠ e.1) (hcd : d.1 ≠ e.1) (x y : BitVec 64)
    (k : Nat) (hk : k < 16) :
    (G b v a c d e x y)[k] =
      if c.1 = k then (mix b v[a.1] v[c.1] v[d.1] v[e.1] x y).2.1
      else if d.1 = k then (mix b v[a.1] v[c.1] v[d.1] v[e.1] x y).2.2.1
      else if e.1 = k then (mix b v[a.1] v[c.1] v[d.1] v[e.1] x y).2.2.2
      else if a.1 = k then (mix b v[a.1] v[c.1] v[d.1] v[e.1] x y).1 else v[k] :=
  G_get b v hab hac had hbc hbd hcd x y k hk

/-- The four column `G`s of a round. -/
theorem columns_eq (x y : Nat → BitVec 64) (v : Work 64) :
    G b (G b (G b (G b v 0 4 8 12 (x 0) (y 0)) 1 5 9 13 (x 1) (y 1)) 2 6 10 14 (x 2) (y 2))
      3 7 11 15 (x 3) (y 3) = mixCols x y v := by
  apply Vector.ext
  intro j hj
  simp only [mixCols_get]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := cases16 hj
  all_goals
    simp (disch := decide) only [G_get', val_lit, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, mixAt]

/-- The four diagonal `G`s of a round, with the message words `x i` and `y i`
of diagonal `i`. -/
theorem diagonals_eq (x y : Nat → BitVec 64) (v : Work 64) :
    G b (G b (G b (G b v 0 5 10 15 (x 0) (y 0)) 1 6 11 12 (x 1) (y 1)) 2 7 8 13 (x 2) (y 2))
      3 4 9 14 (x 3) (y 3) =
      rotOut (mixCols (fun q => x ((q + 3) % 4)) (fun q => y ((q + 3) % 4)) (rotIn v)) := by
  apply Vector.ext
  intro j hj
  simp only [rotOut_get, rotIn_get, mixCols_get]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := cases16 hj
  all_goals
    simp (disch := decide) only [G_get', val_lit, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceMul, Nat.reduceEqDiff, ↓reduceIte, mixAt]

/-- Round `r` of BLAKE2b on four columns: the column `G`s, then the diagonal
ones. -/
theorem round_lanes (m : Block 64) (v : Work 64) (r : Nat) :
    round b m v r =
      rotOut (mixCols (fun q => m (sigmaAt r (8 + 2 * ((q + 3) % 4))))
        (fun q => m (sigmaAt r (9 + 2 * ((q + 3) % 4))))
        (rotIn (mixCols (fun q => m (sigmaAt r (2 * q))) (fun q => m (sigmaAt r (2 * q + 1))) v))) := by
  rw [← diagonals_eq (fun i => m (sigmaAt r (8 + 2 * i))) (fun i => m (sigmaAt r (9 + 2 * i))),
    ← columns_eq]
  rfl

end VG.Proof.Blake2
