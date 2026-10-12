module

/-!
# Ed448: the point formulas as field programs

Target-independent: a field program is a list of operations on numbered
field-element slots (`FOp`), and each target runs it with its own field
arithmetic. `doubleOps` and `addOps` are RFC 8032 §5.2.4's doubling and
addition of projective points, on the slots every Ed448 base-point
multiplication uses: `R` in slots 0–2, `T` in 3–5, `Q` in 8–10, `d` in 11,
and temporaries in 12–20.
-/

@[expose] public section

namespace VG.Impl.Ed448

/-- A field operation on slots (numbered from 0). -/
inductive FOp where
  | mul (o a b : Nat)
  | sqr (o a : Nat)
  | add (o a b : Nat)
  | sub (o a b : Nat)
  deriving DecidableEq, Repr

/-- `R = 2R` in slots 0–2 (RFC 8032 §5.2.4, doubling), with the temporaries
12–19: `B = (X + Y)²`, `C = X²`, `D = Y²`, `E = C + D`, `H = Z²`,
`J = E - 2H`, `X = (B - E) J`, `Y = E (C - D)`, `Z = E J`. -/
def doubleOps : List FOp := [
  .add 12 0 1, .sqr 12 12, .sqr 13 0, .sqr 14 1, .add 15 13 14, .sqr 16 2,
  .add 17 16 16, .sub 17 15 17, .sub 18 12 15, .mul 0 18 17, .sub 19 13 14, .mul 1 15 19,
  .mul 2 15 17]

/-- `T = R + Q` into slots 3–5, for `R` in slots 0–2, `Q` in slots 8–10 and
`d` in slot 11 (RFC 8032 §5.2.4, addition), with the temporaries 12–20:
`A = Z₁Z₂`, `B = A²`, `C = X₁X₂`, `D = Y₁Y₂`, `E = dCD`, `F = B - E`,
`G = B + E`, `H = (X₁ + Y₁)(X₂ + Y₂)`, `X₃ = AF(H - C - D)`,
`Y₃ = AG(D - C)`, `Z₃ = FG`. -/
def addOps : List FOp := [
  .mul 12 2 10, .sqr 13 12, .mul 14 0 8, .mul 15 1 9, .mul 16 11 14, .mul 16 16 15,
  .sub 17 13 16, .add 18 13 16, .add 19 0 1, .add 20 8 9, .mul 19 19 20, .mul 20 12 17,
  .sub 19 19 14, .sub 19 19 15, .mul 3 20 19, .mul 20 12 18, .sub 19 15 14, .mul 4 20 19,
  .mul 5 17 18]

/-! ## Verification's equation -/

/-- `R = 2R` in slots `x`, `y`, `z` (the doubling of `doubleOps`). -/
def doubleAt (x y z : Nat) : List FOp := [
  .add 12 x y, .sqr 12 12, .sqr 13 x, .sqr 14 y, .add 15 13 14, .sqr 16 z,
  .add 17 16 16, .sub 17 15 17, .sub 18 12 15, .mul x 18 17, .sub 19 13 14, .mul y 15 19,
  .mul z 15 17]

/-- `T = R + (x : y : 1)` into slots 3–5 (the addition of `addOps`, with the
second point in slots `x`, `y` and 10). -/
def addAt (x y : Nat) : List FOp := [
  .mul 12 2 10, .sqr 13 12, .mul 14 0 x, .mul 15 1 y, .mul 16 11 14, .mul 16 16 15,
  .sub 17 13 16, .add 18 13 16, .add 19 0 1, .add 20 x y, .mul 19 19 20, .mul 20 12 17,
  .sub 19 19 14, .sub 19 19 15, .mul 3 20 19, .mul 20 12 18, .sub 19 15 14, .mul 4 20 19,
  .mul 5 17 18]

/-- From `y` in slot `yo` (with 1 in slot 10 and `d` in slot 11): `v` in
slot 3, `u` in slot 13, `u³v` in slot `xo`, and `u⁵v³` in slot 12. -/
def decodeUV (yo xo : Nat) : List FOp :=
  [.sqr 12 yo, .sub 13 12 10, .mul 3 11 12, .sub 3 3 10, .mul 4 13 3, .sqr 4 4, .sqr 5 13,
    .mul 5 5 13, .mul xo 5 3, .mul 12 xo 4]

end VG.Impl.Ed448
