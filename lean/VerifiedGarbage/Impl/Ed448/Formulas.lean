/-!
# Ed448: the point formulas as field programs

Target-independent: a field program is a list of operations on numbered
field-element slots (`FOp`), and each target runs it with its own field
arithmetic. `doubleOps` and `addOps` are RFC 8032 §5.2.4's doubling and
addition of projective points, on the slots every Ed448 base-point
multiplication uses: `R` in slots 0–2, `T` in 3–5, `Q` in 8–10, `d` in 11,
and temporaries in 12–20.
-/

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

end VG.Impl.Ed448
