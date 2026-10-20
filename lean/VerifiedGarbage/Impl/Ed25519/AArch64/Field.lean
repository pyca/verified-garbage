module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Word
public import VerifiedGarbage.Spec.X25519

/-! Extended Edwards formulas on the four-word field representation.
Slots 0–21 occupy bytes 64–767 of the eight-KiB workspace. -/

@[expose] public section

namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

abbrev Slot := Fin 22

def offset (s : Slot) : Nat := 64 + 32 * s.val

def constWords (v : Spec.X25519.Fe) : List Instr :=
  const64 .x4 (BitVec.ofNat 64 v.val) ++
  const64 .x5 (BitVec.ofNat 64 (v.val / 2 ^ 64)) ++
  const64 .x6 (BitVec.ofNat 64 (v.val / 2 ^ 128)) ++
  const64 .x7 (BitVec.ofNat 64 (v.val / 2 ^ 192))

def constField (o : Slot) (v : Spec.X25519.Fe) : List Instr := constWords v ++ store4 (offset o)

def copyField (o a : Slot) : List Instr := loads (offset a) .x4 .x5 .x6 .x7 ++ store4 (offset o)

/-- Small field programs, lowered to the existing verified integer code. -/
inductive FieldOp where
  | copy (out a : Slot)
  | const (out : Slot) (v : Spec.X25519.Fe)
  | mul (out a b : Slot)
  | sqr (out a : Slot)
  | add (out a b : Slot)
  | sub (out a b : Slot)
  deriving DecidableEq

def FieldOp.code : FieldOp → List Instr
  | .copy o a => copyField o a
  | .const o v => constField o v
  | .mul o a b => fieldMul (offset o) (offset a) (offset b)
  | .sqr o a => fieldSqr (offset o) (offset a)
  | .add o a b => fieldAdd (offset o) (offset a) (offset b)
  | .sub o a b => fieldSub (offset o) (offset a) (offset b)

/-- The slot `op` writes. -/
def FieldOp.out : FieldOp → Slot
  | .copy o _ | .const o _ | .mul o _ _ | .sqr o _ | .add o _ _ | .sub o _ _ => o

/-- The slots holding values below `2²⁵⁵ + 2¹³⁶` after `op`, if `S` did before
it: products and squares (`reduceWide` stores them below `2²⁵⁵ + 2¹³⁵`),
constants, and copies of such slots. -/
def FieldOp.small (op : FieldOp) (S : Slot → Bool) : Slot → Bool :=
  match op with
  | .copy o a => fun i => if i = o then S a else S i
  | .const o _ | .mul o _ _ | .sqr o _ => fun i => if i = o then true else S i
  | .add o _ _ | .sub o _ _ => fun i => if i = o then false else S i

/-- `op`, adding or subtracting with one fold of the carry when the slots `S`
hold small values: both operands of an addition (their sum is below
`2²⁵⁷ − 38`), the subtrahend of a subtraction (below `2²⁵⁶ − 38`). -/
def FieldOp.codeS (S : Slot → Bool) : FieldOp → List Instr
  | .add o a b => if S a && S b then fieldAdd1 (offset o) (offset a) (offset b)
      else fieldAdd (offset o) (offset a) (offset b)
  | .sub o a b => if S b then fieldSub1 (offset o) (offset a) (offset b)
      else fieldSub (offset o) (offset a) (offset b)
  | op => op.code

/-- `ops`, with the slots `S` small before them. -/
def fieldCodeFrom : (Slot → Bool) → List FieldOp → List Instr
  | _, [] => []
  | S, op :: ops => op.codeS S ++ fieldCodeFrom (op.small S) ops

/-- `ops`: an addition or subtraction of values its earlier operations
multiplied, squared or set folds the carry once (`FieldOp.codeS`). -/
def fieldCode (ops : List FieldOp) : List Instr := fieldCodeFrom (fun _ => false) ops

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

/-- Double the first point: the complete addition formula on two equal
inputs, with its products of equal factors as squarings. -/
def pointDoubleOps : List FieldOp := [
  .sub 8 1 0, .sqr 8 8,
  .add 9 1 0, .sqr 9 9,
  .sqr 10 3, .mul 10 10 16, .add 10 10 10,
  .sqr 11 2, .add 11 11 11,
  .sub 12 9 8, .sub 13 11 10, .add 14 11 10, .add 15 9 8,
  .mul 0 12 13, .mul 1 14 15, .mul 2 13 14, .mul 3 12 15]

def pointDouble : List Instr := fieldCode pointDoubleOps

end VG.Impl.Ed25519.AArch64
