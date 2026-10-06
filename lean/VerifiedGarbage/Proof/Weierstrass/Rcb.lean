/-!
# Complete projective addition (Renes, Costello and Batina)

Algorithm 1 of Renes, Costello and Batina, "Complete addition formulas for
prime order elliptic curves" (EUROCRYPT 2016): the sum of two points
`(X₁ : Y₁ : Z₁)` and `(X₂ : Y₂ : Z₂)` of `Y²Z = X³ + aXZ² + bZ³`, for any
`a`, with `b3 = 3b`, in its 40 steps, as the implementations compute it:
over any commutative ring of Lean's core (`Lean.Grind.CommRing`), so that
the implementations' proofs compute it in `Fin p` without importing
Mathlib's algebra, which only the proofs of the group law need.
-/

namespace VG.Proof.Weierstrass

variable {F : Type _} [Lean.Grind.CommRing F]

/-- Algorithm 1, in its stated order. -/
def rcbAdd (a b3 X1 Y1 Z1 X2 Y2 Z2 : F) : F × F × F :=
  let t0 := X1 * X2
  let t1 := Y1 * Y2
  let t2 := Z1 * Z2
  let t3 := X1 + Y1
  let t4 := X2 + Y2
  let t3 := t3 * t4
  let t4 := t0 + t1
  let t3 := t3 - t4
  let t4 := X1 + Z1
  let t5 := X2 + Z2
  let t4 := t4 * t5
  let t5 := t0 + t2
  let t4 := t4 - t5
  let t5 := Y1 + Z1
  let X3 := Y2 + Z2
  let t5 := t5 * X3
  let X3 := t1 + t2
  let t5 := t5 - X3
  let Z3 := a * t4
  let X3 := b3 * t2
  let Z3 := X3 + Z3
  let X3 := t1 - Z3
  let Z3 := t1 + Z3
  let Y3 := X3 * Z3
  let t1 := t0 + t0
  let t1 := t1 + t0
  let t2 := a * t2
  let t4 := b3 * t4
  let t1 := t1 + t2
  let t2 := t0 - t2
  let t2 := a * t2
  let t4 := t4 + t2
  let t0 := t1 * t4
  let Y3 := Y3 + t0
  let t0 := t5 * t4
  let X3 := t3 * X3
  let X3 := X3 - t0
  let t0 := t3 * t1
  let Z3 := t5 * Z3
  let Z3 := Z3 + t0
  (X3, Y3, Z3)


/-- Algorithm 4 (`a = -3`), in its stated order, with `b`. -/
def rcbAdd3 (b X1 Y1 Z1 X2 Y2 Z2 : F) : F × F × F :=
  let t0 := X1 * X2; let t1 := Y1 * Y2; let t2 := Z1 * Z2; let t3 := X1 + Y1; let t4 := X2 + Y2
  let t3 := t3 * t4; let t4 := t0 + t1; let t3 := t3 - t4; let t4 := Y1 + Z1; let X3 := Y2 + Z2
  let t4 := t4 * X3; let X3 := t1 + t2; let t4 := t4 - X3; let X3 := X1 + Z1; let Y3 := X2 + Z2
  let X3 := X3 * Y3; let Y3 := t0 + t2; let Y3 := X3 - Y3; let Z3 := b * t2; let X3 := Y3 - Z3
  let Z3 := X3 + X3; let X3 := X3 + Z3; let Z3 := t1 - X3; let X3 := t1 + X3; let Y3 := b * Y3
  let t1 := t2 + t2; let t2 := t1 + t2; let Y3 := Y3 - t2; let Y3 := Y3 - t0; let t1 := Y3 + Y3
  let Y3 := t1 + Y3; let t1 := t0 + t0; let t0 := t1 + t0; let t0 := t0 - t2; let t1 := t4 * Y3
  let t2 := t0 * Y3; let Y3 := X3 * Z3; let Y3 := Y3 + t2; let X3 := t3 * X3; let X3 := X3 - t1
  let Z3 := t4 * Z3; let t1 := t3 * t0; let Z3 := Z3 + t1
  (X3, Y3, Z3)

/-- Algorithm 4 is Algorithm 1 with `a = -3` and `3b`. -/
theorem rcbAdd3_eq (b X1 Y1 Z1 X2 Y2 Z2 : F) :
    rcbAdd3 b X1 Y1 Z1 X2 Y2 Z2 = rcbAdd (-3) (3 * b) X1 Y1 Z1 X2 Y2 Z2 := by
  simp only [rcbAdd3, rcbAdd, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- Algorithm 5 (mixed addition, `a = -3`: the second point is `(X₂ : Y₂ : 1)`),
in its stated order, with `b`. -/
def rcbAdd3m (b X1 Y1 Z1 X2 Y2 : F) : F × F × F :=
  let t0 := X1 * X2; let t1 := Y1 * Y2; let t3 := X2 + Y2; let t4 := X1 + Y1; let t3 := t3 * t4
  let t4 := t0 + t1; let t3 := t3 - t4; let t4 := Y2 * Z1; let t4 := t4 + Y1; let Y3 := X2 * Z1
  let Y3 := Y3 + X1; let Z3 := b * Z1; let X3 := Y3 - Z3; let Z3 := X3 + X3; let X3 := X3 + Z3
  let Z3 := t1 - X3; let X3 := t1 + X3; let Y3 := b * Y3; let t1 := Z1 + Z1; let t2 := t1 + Z1
  let Y3 := Y3 - t2; let Y3 := Y3 - t0; let t1 := Y3 + Y3; let Y3 := t1 + Y3; let t1 := t0 + t0
  let t0 := t1 + t0; let t0 := t0 - t2; let t1 := t4 * Y3; let t2 := t0 * Y3; let Y3 := X3 * Z3
  let Y3 := Y3 + t2; let X3 := t3 * X3; let X3 := X3 - t1; let Z3 := t4 * Z3; let t1 := t3 * t0
  let Z3 := Z3 + t1
  (X3, Y3, Z3)

/-- Algorithm 5 is Algorithm 4 with `Z₂ = 1`. -/
theorem rcbAdd3m_eq (b X1 Y1 Z1 X2 Y2 : F) :
    rcbAdd3m b X1 Y1 Z1 X2 Y2 = rcbAdd3 b X1 Y1 Z1 X2 Y2 1 := by
  simp only [rcbAdd3m, rcbAdd3, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- Algorithm 6 (doubling, `a = -3`), in its stated order, with `b`. -/
def rcbDbl3 (b X Y Z : F) : F × F × F :=
  let t0 := X * X; let t1 := Y * Y; let t2 := Z * Z; let t3 := X * Y; let t3 := t3 + t3
  let Z3 := X * Z; let Z3 := Z3 + Z3; let Y3 := b * t2; let Y3 := Y3 - Z3; let X3 := Y3 + Y3
  let Y3 := X3 + Y3; let X3 := t1 - Y3; let Y3 := t1 + Y3; let Y3 := X3 * Y3; let X3 := X3 * t3
  let t3 := t2 + t2; let t2 := t2 + t3; let Z3 := b * Z3; let Z3 := Z3 - t2; let Z3 := Z3 - t0
  let t3 := Z3 + Z3; let Z3 := Z3 + t3; let t3 := t0 + t0; let t0 := t3 + t0; let t0 := t0 - t2
  let t0 := t0 * Z3; let Y3 := Y3 + t0; let t0 := Y * Z; let t0 := t0 + t0; let Z3 := t0 * Z3
  let X3 := X3 - Z3; let Z3 := t0 * t1; let Z3 := Z3 + Z3; let Z3 := Z3 + Z3
  (X3, Y3, Z3)

/-- Algorithm 6 is Algorithm 1's sum of a point and itself, for a point of
`Y²Z = X³ - 3XZ² + bZ³` (its `Z` differs by `6Y` times the equation). -/
theorem rcbDbl3_eq (b X Y Z : F) (hE : Y * Y * Z = X * X * X - 3 * X * Z * Z + b * Z * Z * Z) :
    rcbDbl3 b X Y Z = rcbAdd (-3) (3 * b) X Y Z X Y Z := by
  simp only [rcbDbl3, rcbAdd, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

end VG.Proof.Weierstrass
