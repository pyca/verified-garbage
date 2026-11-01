module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.MulFn

/-!
# Ed25519 on PPC64LE: field programs

Extended Edwards formulas on eight-limb field elements, as ARMv7's
(`Impl/Ed25519/Arm/Field.lean`). Slots 0–21 occupy bytes 64–767 of the
eight-KiB working space, 32 bytes each, as `Proof/Ed25519/Point32Contract.lean` and
`Proof/X25519/Field32Contract.lean` place their operands: the first point at slots
0–3 (byte 64), the second at 4–7 (byte 192), the temporaries of an addition
at 8–15 (bytes 320–575) and `d` at slot 16 (byte 576).
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE
open VG.PPC64LE

abbrev Slot := Fin 22

def offset (s : Slot) : Nat := 64 + 32 * s.val

/-- Word `k` of `v`, as `lis` and `ori` build it and `stw` stores it. -/
def constLimb (o : Slot) (v : Spec.X25519.Fe) (k : Nat) : List Instr :=
  [.lis .r7 (BitVec.ofNat 16 (v.val / 2 ^ (32 * k + 16))),
    .ori .r7 .r7 (BitVec.ofNat 16 (v.val / 2 ^ (32 * k))), .store .w .r7 .r6 (offset o + 4 * k)]

def constField (o : Slot) (v : Spec.X25519.Fe) : List Instr :=
  (List.range 8).flatMap (constLimb o v)

def copyLimb (o a : Slot) (k : Nat) : List Instr :=
  [.load .w .r7 .r6 (offset a + 4 * k), .store .w .r7 .r6 (offset o + 4 * k)]

def copyField (o a : Slot) : List Instr := (List.range 8).flatMap (copyLimb o a)

/-- Small field programs, lowered to the existing verified integer code. `mulc` is `mul` as a
call of `vg_gf25519_r32_mul`, for code off the hot paths. -/
inductive FieldOp where
  | copy (out a : Slot)
  | const (out : Slot) (v : Spec.X25519.Fe)
  | mul (out a b : Slot)
  | mulc (out a b : Slot)
  | add (out a b : Slot)
  | sub (out a b : Slot)
  deriving DecidableEq

/-- Whether an operation's code is inlined: all but `mulc`, a call. -/
def FieldOp.inline : FieldOp → Bool
  | .mulc .. => false
  | _ => true

def FieldOp.code : FieldOp → Prog isa
  | .copy o a => .block (copyField o a)
  | .const o v => .block (constField o v)
  | .mul o a b => VG.Impl.Ed25519.PPC64LE.mul (offset o) (offset a) (offset b)
  | .mulc o a b => mulCall (offset o) (offset a) (offset b)
  | .add o a b => .block (VG.Impl.Ed25519.PPC64LE.add (offset o) (offset a) (offset b))
  | .sub o a b => .block (VG.Impl.Ed25519.PPC64LE.sub (offset o) (offset a) (offset b))

def fieldCode : List FieldOp → Prog isa
  | [] => .block []
  | op :: ops => .seq op.code (fieldCode ops)

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

def pointAdd : Prog isa := fieldCode pointAddOps

end VG.Impl.Ed25519.PPC64LE
