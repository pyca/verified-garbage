import VerifiedGarbage.Impl.X25519.X86_64
import VerifiedGarbage.Spec.Ed25519

/-!
# Ed25519 field operations on x86-64

Field elements reuse X25519's four-word representation and arithmetic.
Slots 2 through 23 occupy bytes [64, 768) of the scratch buffer; the
first 64 bytes are reserved for saved registers and pointers.
-/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (loads store4)

abbrev Slot := Fin 22

/-- The field multiplications the code is emitted with (X25519's): the baseline's, or BMI2
and ADX's. -/
abbrev Arith := VG.Impl.X25519.X86_64.Field

def offset (s : Slot) : Nat := 64 + 32 * s.val

def constWords (v : Spec.X25519.Fe) : List Instr :=
  [.movImm64 .r8 (BitVec.ofNat 64 v.val),
    .movImm64 .r9 (BitVec.ofNat 64 (v.val / 2 ^ 64)),
    .movImm64 .r10 (BitVec.ofNat 64 (v.val / 2 ^ 128)),
    .movImm64 .r11 (BitVec.ofNat 64 (v.val / 2 ^ 192))]

def constField (o : Slot) (v : Spec.X25519.Fe) : List Instr := constWords v ++ store4 (offset o)

def copyField (o a : Slot) : List Instr :=
  loads (offset a) .r8 .r9 .r10 .r11 ++ store4 (offset o)

/-- Small field programs, lowered to the existing verified integer code. -/
inductive FieldOp where
  | copy (out a : Slot)
  | const (out : Slot) (v : Spec.X25519.Fe)
  | mul (out a b : Slot)
  | sqr (out a : Slot)
  | add (out a b : Slot)
  | sub (out a b : Slot)
  /-- `2ab`: the doubling in the product's reduction (`Field.mul2`). -/
  | mul2 (out a b : Slot)
  /-- `2a²` (`Field.sqr2`). -/
  | sqr2 (out a : Slot)
  deriving DecidableEq

def FieldOp.code (fld : Arith) : FieldOp → List Instr
  | .copy o a => copyField o a
  | .const o v => constField o v
  | .mul o a b => fld.mul (offset o) (offset a) (offset b)
  | .sqr o a => fld.sqr (offset o) (offset a)
  | .add o a b => Impl.X25519.X86_64.add (offset o) (offset a) (offset b)
  | .sub o a b => Impl.X25519.X86_64.sub (offset o) (offset a) (offset b)
  | .mul2 o a b => fld.mul2 (offset o) (offset a) (offset b)
  | .sqr2 o a => fld.sqr2 (offset o) (offset a)

/-- `FieldOp.code`, but with the sums and differences folded once (`addL`, `subL`) if
`lazy`: correct when one operand of each sum, and the subtrahend of each difference,
is at most `2p`, as a product is. -/
def FieldOp.codeB (fld : Arith) (lazy : Bool) : FieldOp → List Instr
  | .add o a b => if lazy then Impl.X25519.X86_64.addL (offset o) (offset a) (offset b)
      else Impl.X25519.X86_64.add (offset o) (offset a) (offset b)
  | .sub o a b => if lazy then Impl.X25519.X86_64.subL (offset o) (offset a) (offset b)
      else Impl.X25519.X86_64.sub (offset o) (offset a) (offset b)
  | op => op.code fld

/-- The slot an operation writes. -/
def FieldOp.out : FieldOp → Slot
  | .copy o _ | .const o _ | .mul o _ _ | .sqr o _ | .add o _ _ | .sub o _ _ | .mul2 o _ _
  | .sqr2 o _ => o

/-- The operation's result is at most `2p`: a product, or a constant. -/
def FieldOp.bnd : FieldOp → Bool
  | .mul .. | .sqr .. | .const .. => true
  | _ => false

/-- The slots holding at most `2p` after `op`, if `B` did before it. -/
def bndStep (op : FieldOp) (B : Slot → Bool) (i : Slot) : Bool := if i = op.out then op.bnd else B i

/-- `op`'s operands are bounded as `codeB lazy` needs. -/
def opOk (lazy : Bool) (op : FieldOp) (B : Slot → Bool) : Bool :=
  match lazy, op with
  | true, .add _ a b => B a || B b
  | true, .sub _ _ b => B b
  | _, _ => true

/-- The slots bounded after `ops`, if `B` were before them. -/
def bndOut : List FieldOp → (Slot → Bool) → Slot → Bool
  | [], B => B
  | op :: ops, B => bndOut ops (bndStep op B)

/-- The field program `ops`, with the slots `B` at most `2p` before it: each sum or
difference is folded once (`FieldOp.codeB`) where an operand of the sum, or the
subtrahend, is bounded (`opOk`), as products and constants are (`bndStep`). -/
def fieldCodeFrom (fld : Arith) : (Slot → Bool) → List FieldOp → List Instr
  | _, [] => []
  | B, op :: ops => op.codeB fld (opOk true op B) ++ fieldCodeFrom fld (bndStep op B) ops

/-- The field program `ops`, its sums and differences of products folded once
(`fieldCodeFrom`, from no slot bounded). -/
def fieldCode (fld : Arith) (ops : List FieldOp) : List Instr := fieldCodeFrom fld (fun _ => false) ops

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

def pointAdd (fld : Arith) : List Instr := fieldCode fld pointAddOps

/-- Double the first point, using the complete addition formula on two
equal inputs. Uses precisely the same formula as the specification. -/
def pointDoubleOps : List FieldOp := [
  .sub 8 1 0, .sqr 8 8,
  .add 9 1 0, .sqr 9 9,
  .mul 10 3 16, .add 10 10 10, .mul 10 10 3,
  .add 11 2 2, .mul 11 11 2,
  .sub 12 9 8, .sub 13 11 10, .add 14 11 10, .add 15 9 8,
  .mul 0 12 13, .mul 1 14 15, .mul 2 13 14, .mul 3 12 15]

def pointDouble (fld : Arith) : List Instr := fieldCode fld pointDoubleOps

end VG.Impl.Ed25519.X86_64
