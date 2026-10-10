import VerifiedGarbage.Impl.X25519.X86
import VerifiedGarbage.Spec.Ed25519

/-! Extended Edwards formulas on the eight-word field representation.
Slots 0–21 occupy bytes 64–767 of the eight-KiB workspace. -/

namespace VG.Impl.Ed25519.X86
open VG.X86

abbrev Slot := Fin 22

def offset (s : Slot) : Nat := 64 + 32 * s.val

def constField (o : Slot) (v : Spec.X25519.Fe) : List Instr :=
  (List.range 8).flatMap fun k =>
    [.mov .eax (.imm (BitVec.ofNat 32 (v.val / (2 ^ 32) ^ k))),
      .store (VG.Impl.X25519.X86.sc (offset o + 4 * k)) .eax]

def copyField (o a : Slot) : List Instr := VG.Impl.X25519.X86.copy (offset o) (offset a)

/-- Small field programs, lowered to the existing verified integer code. -/
inductive FieldOp where
  | copy (out a : Slot)
  | const (out : Slot) (v : Spec.X25519.Fe)
  | mul (out a b : Slot)
  | add (out a b : Slot)
  | sub (out a b : Slot)
  deriving DecidableEq

def FieldOp.code : FieldOp → List Instr
  | .copy o a => copyField o a
  | .const o v => constField o v
  | .mul o a b => VG.Impl.X25519.X86.mul (offset o) (offset a) (offset b)
  | .add o a b => VG.Impl.X25519.X86.add (offset o) (offset a) (offset b)
  | .sub o a b => VG.Impl.X25519.X86.sub (offset o) (offset a) (offset b)

def fieldCode (ops : List FieldOp) : List Instr := ops.flatMap FieldOp.code

/-- Add the points in slots 0–3 and 4–7 into slots 0–3. The coordinates
are X,Y,Z,T. Slot 16 holds d; slots 8–15 are temporary. Both points are
read before the result overwrites the first. -/
def pointAddOps : List FieldOp := [
  .sub 8 1 0, .sub 9 5 4, .mul 8 8 9,
  .add 9 1 0, .add 10 5 4, .mul 9 9 10,
  .mul 10 3 16, .add 10 10 10, .mul 10 10 7,
  .add 11 2 2, .mul 11 11 6,
  .sub 12 9 8, .sub 13 11 10, .add 14 11 10, .add 15 9 8,
  .mul 0 12 13, .mul 1 14 15, .mul 2 13 14, .mul 3 12 15]

def pointAdd : List Instr := fieldCode pointAddOps

/-- Double the first point, using the complete addition formula on two
equal inputs. Uses precisely the same formula as the specification. -/
def pointDoubleOps : List FieldOp := [
  .sub 8 1 0, .mul 8 8 8,
  .add 9 1 0, .mul 9 9 9,
  .mul 10 3 16, .add 10 10 10, .mul 10 10 3,
  .add 11 2 2, .mul 11 11 2,
  .sub 12 9 8, .sub 13 11 10, .add 14 11 10, .add 15 9 8,
  .mul 0 12 13, .mul 1 14 15, .mul 2 13 14, .mul 3 12 15]

def pointDouble : List Instr := fieldCode pointDoubleOps

/-- Doubles slots 0–3 in place, to RFC 8032's coordinates (§5.1.4: `A = X²`, `B = Y²`,
`C = 2Z²`, `H = A + B`, `E = H - (X + Y)²`, `G = A - B`, `F = C + G`, and `X = EF`, `Y = GH`,
`Z = FG`, `T = EH`), with `-E = 2XY` from one product rather than a square and two additions:
`-G = B - A`, `-F = -G - C` and `-H = -G - B - B`, so that `X = (-E)(-F)`, `Y = (-G)(-H)`,
`Z = (-F)(-G)` and `T = (-E)(-H)`: eight products, without `d`
(`vg_ed25519_r32_double`). Slots 8–14 are temporary. -/
def pointDoubleRfcOps : List FieldOp := [
  .mul 8 0 0, .mul 9 1 1, .mul 10 2 2, .add 10 10 10, .mul 11 0 1, .add 11 11 11,
  .sub 12 9 8, .sub 13 12 10, .sub 14 12 9, .sub 14 14 9,
  .mul 0 11 13, .mul 1 12 14, .mul 2 13 12, .mul 3 11 14]

/-- Add the affine cached point in slots 4–6 (`[Y - X, Y + X, 2dT]` of a point with `Z = 1`,
so its `2Z` is `2` and `Z₁ · 2Z₂` is `Z₁ + Z₁`) to slots 0–3, in place: `a = (Y₁ - X₁)(Y₂ - X₂)`,
`b = (Y₁ + X₁)(Y₂ + X₂)`, `c = T₁ · 2dT₂`, `dd = 2Z₁`, `h = b + a`, `e = b - a`, `g = dd + c`,
`f = dd - c`, and `(ef, gh, fg, eh)`: seven products (`vg_ed25519_r32_add_affine`). Slots
8–12 are temporary. -/
def pointAddAffineOps : List FieldOp := [
  .sub 8 1 0, .mul 8 8 4, .add 9 1 0, .mul 9 9 5, .mul 10 3 6, .add 11 2 2,
  .add 12 9 8, .sub 8 9 8, .add 9 11 10, .sub 10 11 10,
  .mul 0 8 10, .mul 1 9 12, .mul 2 10 9, .mul 3 8 12]

end VG.Impl.Ed25519.X86
