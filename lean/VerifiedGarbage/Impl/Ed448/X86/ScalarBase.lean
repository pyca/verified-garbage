import VerifiedGarbage.Impl.Ed448.Formulas
import VerifiedGarbage.Impl.Ed448.X86.Scalar
import VerifiedGarbage.Spec.Ed448

/-!
# Ed448 base-point multiplication on x86 (32-bit)

`vg_ed448_scalar_base(out = [esp + 4], scalar = [esp + 8], scratch = [esp + 12])`:
the encoding of `[s]B` for the 456-bit little-endian scalar `s`, without
pruning.

Field elements are X448's on this target (twenty-eight 16-bit limbs in the
128-byte slots of the working space, `Impl/X448/X86.lean`), and so is the
field arithmetic: multiplications (and squarings, as multiplications of a
slot by itself), additions and subtractions, which are calls of the field
functions `vg_gf448_r16_*` (their arguments in the 20 bytes of stack below
the return address), the constant-time swap, the inversion, the full
reduction of slot 1 and its output. Points are the
specification's projective coordinates `(X : Y : Z)`. As in X448, `edi`
holds the working space and `esi` the loop counter; the callee-saved
registers are saved in the working space's first 16 bytes
(`Impl/Ed448/X86/Scalar.lean`'s `save`).

Every slot is initialized: `R` (slots 0–2) to the neutral point
`(0 : 1 : 1)`, `B` (slots 8–10) to the base point, slot 11 to `d`, and the
others to zero. The scalar's bits are expanded into bytes at `BITS` (byte
`t` is bit `t`), as X448 expands its scalar. Then, from the top bit down,
`R` is doubled and `T = R + B` computed into slots 3–5 with RFC 8032
§5.2.4's formulas (`Impl/Ed448/Formulas.lean`'s `doubleOps` and `addOps`),
and `T` swapped into `R` with the mask of the bit: the same operations for
every bit, whatever its value. Finally `R` is encoded (§5.2.2): `Z` inverted
with X448's addition chain, `x = X/Z` (into slot 1) fully reduced and its low
bit written as the top bit of the output's 57th byte, and `y = Y/Z` fully
reduced and written as its first 56 bytes.

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

namespace VG.Impl.Ed448.X86

open VG.X86
open VG.Impl.X448.X86 (at_ ld st slot BITS X2 Op ops cswap freeze invert bitJ copy)

/-! ## Field programs on the slots -/

/-- A field operation (`Impl/Ed448/Formulas.lean`) as X448's. -/
def toOp : FOp → Impl.X448.X86.Op
  | .mul o a b => .mul (slot o) (slot a) (slot b)
  | .sqr o a => .mul (slot o) (slot a) (slot a)
  | .add o a b => .add (slot o) (slot a) (slot b)
  | .sub o a b => .sub (slot o) (slot a) (slot b)

def field (l : List FOp) : Prog isa := ops (l.map toOp)

/-! ## Initial slots -/

/-- The initial value of slot `i`: `R = (0 : 1 : 1)`, `B` the base point and
`d`, and zero elsewhere. -/
def initVal (i : Nat) : Nat :=
  if i = 0 then Spec.Ed448.identity.X.val
  else if i = 1 then Spec.Ed448.identity.Y.val
  else if i = 2 then Spec.Ed448.identity.Z.val
  else if i = 8 then Spec.Ed448.basePoint.X.val
  else if i = 9 then Spec.Ed448.basePoint.Y.val
  else if i = 10 then Spec.Ed448.basePoint.Z.val
  else if i = 11 then Spec.Ed448.d.val
  else 0

/-- Limb `k` of slot `i`'s initial value. -/
def initLimb (i k : Nat) : Nat := initVal i / 2 ^ (16 * k) % 65536

/-- Limb `k` of slot `i`, through `ebp = edi + 64`, the address of slot 0
(`ebx` is zero). -/
def initStep (i k : Nat) : List Instr :=
  if initLimb i k = 0 then [.store (at_ .ebp (128 * i + 4 * k)) .ebx]
  else [.mov .eax (.imm (BitVec.ofNat 32 (initLimb i k))), .store (at_ .ebp (128 * i + 4 * k)) .eax]

def initSlot (i : Nat) : List Instr := (List.range 28).flatMap (initStep i)

/-- Every slot set to its initial value. The stores are through `ebp`, not
`edi`: the taint analysis records public words it stores at known offsets of
the working space, and the constants (the base point and `d`) would stay in
that record through the whole ladder, slowing every check of a store. -/
def initSlots : List Instr :=
  [.mov .ebp (.reg .edi), .alu .add .ebp (.imm 64), .mov .ebx (.imm 0)] ++
    (List.range 22).flatMap initSlot

/-! ## The scalar's bits -/

/-- Byte `i` of the scalar (at `esi`) expanded to bytes `BITS + 8 i + j`. -/
def baseByte (i : Nat) : List Instr :=
  [.movzx8 .eax (at_ .esi i)] ++ (List.range 8).flatMap (bitJ i)

/-- All 456 bits of the scalar (the argument at `[esp + 8]`). -/
def baseBits : List Instr :=
  .mov .esi (.mem (at_ .esp 8)) :: (List.range 57).flatMap baseByte

/-! ## The loop over the bits -/

/-- `ebx = -BITS[esi]`: the mask of bit `esi`. -/
def baseMask : List Instr :=
  [.mov .ebp (.reg .edi), .alu .add .ebp (.reg .esi), .movzx8 .eax (at_ .ebp BITS),
    .mov .ebx (.imm 0), .alu .sub .ebx (.reg .eax)]

/-- `T` swapped into `R` under the mask of bit `esi`, and the counter
compared with zero. -/
def baseSwap : List Instr :=
  baseMask ++ cswap (slot 0) (slot 3) ++ cswap (slot 1) (slot 4) ++ cswap (slot 2) (slot 5) ++
    [.alu .cmp .esi (.imm 0)]

/-- One bit `t = esi - 1`, from the top: `R = 2R`, `T = R + B`, and `T`
swapped into `R` if bit `t` is set. -/
def baseStep : Prog isa :=
  .seq (.block [.alu .sub .esi (.imm 1)]) <| .seq (field doubleOps) <| .seq (field addOps)
    (.block baseSwap)

/-- The 456 bits, from 455 down to 0. -/
def baseLoop : Prog isa := .seq (.block [.mov .esi (.imm 456)]) (.loop baseStep .ne)

/-! ## The encoding -/

/-- The output's address into `esi`, and the low bit of the fully reduced
`x` (slot 1) as the top bit of its 57th byte. -/
def signBit : List Instr :=
  [.mov .esi (.mem (at_ .esp 4)), ld .eax X2, .alu .and .eax (.imm 1), .shift .ror .eax 25,
    .store8 (at_ .esi 56) .al]

/-- `1/Z` into slot 21, `y = Y/Z` into slot 4 and `x = X/Z` into slot 1; `x`
fully reduced and its low bit written; `y` copied into slot 1, fully reduced
and written to the output's first 56 bytes; then the callee-saved registers
restored. -/
def baseEncode : Prog isa :=
  .seq invert <| .seq (ops [.mul (slot 4) (slot 1) (slot 21), .mul X2 (slot 0) (slot 21)]) <|
    .block (freeze ++ signBit ++ copy X2 (slot 4) ++ freeze ++
      (List.range 28).flatMap Impl.X448.X86.packLimb ++ Impl.X448.X86.restore)

/-- `vg_ed448_scalar_base(out = [esp + 4], scalar = [esp + 8], scratch = [esp + 12])`. -/
def scalarBase : Prog isa :=
  .seq (.block (save 12 ++ initSlots ++ baseBits)) <| .seq baseLoop baseEncode

end VG.Impl.Ed448.X86
