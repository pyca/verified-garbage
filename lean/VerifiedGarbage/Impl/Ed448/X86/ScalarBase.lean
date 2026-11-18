module

public import VerifiedGarbage.Impl.Ed448.Comb
public import VerifiedGarbage.Impl.Ed448.Formulas
public import VerifiedGarbage.Impl.Ed448.X86.Scalar
public import VerifiedGarbage.Spec.Ed448

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
`(0 : 1 : 1)`, `Q` (slots 8–10) to the base point (of which only `Z = 1`, in
slot 10, is used here), slot 11 to `d`, and the others to zero. The scalar's
bits are expanded into bytes at `BITS` (byte `t` is bit `t`), as X448 expands
its scalar.

The multiplication is the four-column comb of `Impl/Ed448/Comb.lean`, whose
table holds the sixteen affine points `[i₀ + 2¹¹⁴ i₁ + 2²²⁸ i₂ + 2³⁴² i₃] B`:
114 rows from the top (`combLoop`), each a doubling of `R` (RFC 8032 §5.2.4's
doubling formulas, `Impl/Ed448/Formulas.lean`'s `doubleOps`), the table entry
of the row's four bits of the scalar, 114 apart, selected into `Q`'s `x` and
`y` (slots 8 and 9), and `T = R + Q` (§5.2.4's addition, `addOps`, into slots
3–5) copied into `R`. The selection scans every entry (`combSelect`): the
slots are zeroed, and each entry's limbs, which are immediates of the code,
are ORed in under the mask of the entry's index being the row's (`selEntry`),
so the same instructions run whatever the bits. Finally `R` is encoded
(§5.2.2): `Z` inverted with X448's addition chain, `x = X/Z` (into slot 1)
fully reduced and its low bit written as the top bit of the output's 57th
byte, and `y = Y/Z` fully reduced and written as its first 56 bytes.

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Ed448.X86

open VG.X86
open VG.Impl.X448.X86 (at_ sc ld st slot BITS X2 Op ops freeze invert bitsLoop copy)

/-! ## Field programs on the slots -/

/-- A field operation (`Impl/Ed448/Formulas.lean`) as X448's. -/
def toOp : FOp → Impl.X448.X86.Op
  | .mul o a b => .mul (slot o) (slot a) (slot b)
  | .sqr o a => .mul (slot o) (slot a) (slot a)
  | .add o a b => .add (slot o) (slot a) (slot b)
  | .sub o a b => .sub (slot o) (slot a) (slot b)

def field (l : List FOp) : Prog isa := ops (l.map toOp)

/-! ## Initial slots -/

/-- The initial value of slot `i`: `R = (0 : 1 : 1)`, `Q` the base point and
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

/-- Limb `k` of slot `i`, through `ebp = edi + 64`, the address of slot 0,
if it is not zero (the slots are zeroed first). -/
def initStep (i k : Nat) : List Instr :=
  if initLimb i k = 0 then []
  else [.mov .eax (.imm (BitVec.ofNat 32 (initLimb i k))), .store (at_ .ebp (128 * i + 4 * k)) .eax]

def initSlot (i : Nat) : List Instr := (List.range 28).flatMap (initStep i)

/-- The 704 words of the slots zeroed, through `ebp` from `edi + 64` (`eax`
counts them down). -/
def zeroSlots : Prog isa :=
  .seq (.block [.mov .ebp (.reg .edi), .alu .add .ebp (.imm 64), .mov .ebx (.imm 0), .mov .eax (.imm 704)])
    (.loop (.block [.store (at_ .ebp 0) .ebx, .alu .add .ebp (.imm 4), .alu .sub .eax (.imm 1)]) .ne)

/-- Every slot set to its initial value. The stores are through `ebp`, not
`edi`: the taint analysis records public words it stores at known offsets of
the working space, and the constants (the base point and `d`) would stay in
that record through the whole ladder, slowing every check of a store. -/
def initSlots : Prog isa :=
  .seq zeroSlots (.block ([.mov .ebp (.reg .edi), .alu .add .ebp (.imm 64)] ++ (List.range 22).flatMap initSlot))

/-! ## The scalar's bits -/

/-- All 456 bits of the scalar (the argument at `[esp + 8]`), by `bitsLoop`. -/
def baseBits : Prog isa := .seq (.block [.mov .esi (.mem (at_ .esp 8))]) (bitsLoop BITS 57)

/-- The callee-saved registers saved, the slots initialized and the scalar's bits. -/
def baseEntry : Prog isa := .seq (.block (save 12)) (.seq initSlots baseBits)

/-! ## The four-column comb -/

/-- Limb `j` of coordinate `c` (0 is `x`, 1 is `y`) of the table's entry `i`. -/
def combLimb (i c j : Nat) : Nat :=
  (if c = 0 then (Comb.entry i).1.val else (Comb.entry i).2.val) / 2 ^ (16 * j) % 65536

/-- The row's index into `ecx`: bits `t`, `t + 114`, `t + 228` and `t + 342` of the scalar
(`t = esi`), as `b₀ + 2 b₁ + 4 b₂ + 8 b₃`, each bit a byte at `ebp + o`, for `ebp = edi + t`. -/
def combDigit (o : Nat) : List Instr :=
  [.mov .ebp (.reg .edi), .alu .add .ebp (.reg .esi), .movzx8 .ecx (at_ .ebp (o + 342)),
    .movzx8 .eax (at_ .ebp (o + 228)), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .eax),
    .movzx8 .eax (at_ .ebp (o + 114)), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .eax),
    .movzx8 .eax (at_ .ebp o), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .eax)]

/-- `ebx = -(ecx = i)`: the mask of entry `i`, for the index `ecx < 16`. -/
def selMask (i : Nat) : List Instr :=
  [.mov .eax (.reg .ecx), .alu .xor .eax (.imm (BitVec.ofNat 32 i)), .alu .sub .eax (.imm 1),
    .shift .shr .eax 31, .mov .ebx (.imm 0), .alu .sub .ebx (.reg .eax)]

/-- The limb `v j`, under the mask `ebx`, ORed into limb `j` of the slot at `o`. -/
def selLimb (o : Nat) (v : Nat → Nat) (j : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 (v j))), .alu .and .eax (.reg .ebx),
    .alu .or .eax (.mem (sc (o + 4 * j))), st .eax (o + 4 * j)]

/-- The twenty-eight limbs `v`, under the mask `ebx`, ORed into the slot at `o`. -/
def selCoord (o : Nat) (v : Nat → Nat) : List Instr := (List.range 28).flatMap (selLimb o v)

/-- Entry `i` ORed into slots 8 (`x`) and 9 (`y`) if it is the row's. -/
def selEntry (i : Nat) : List Instr :=
  selMask i ++ selCoord (slot 8) (combLimb i 0) ++ selCoord (slot 9) (combLimb i 1)

/-- The slot at `o` zeroed (`eax` is zero). -/
def zeroSlot (o : Nat) : List Instr := (List.range 28).flatMap fun j => [st .eax (o + 4 * j)]

/-- Slots 8 and 9 zeroed, then every entry scanned: the row's entry, of index `ecx`, in slots 8
and 9. -/
def combSelect : List Instr :=
  .mov .eax (.imm 0) :: zeroSlot (slot 8) ++ zeroSlot (slot 9) ++ (List.range 16).flatMap selEntry

/-- `T` (slots 3–5) into `R` (slots 0–2). -/
def takeOps : List Op := [.copy (slot 0) (slot 3), .copy (slot 1) (slot 4), .copy (slot 2) (slot 5)]

/-- One row `t = esi - 1`, from the top: `R = 2R`, the table entry of the row's bits selected
into `Q`, `R = R + Q`, and the counter compared with zero. -/
def combStep : Prog isa :=
  .seq (.block [.alu .sub .esi (.imm 1)]) <| .seq (field doubleOps) <|
  .seq (.block (combDigit BITS ++ combSelect)) <|
  .seq (ops (addOps.map toOp ++ takeOps)) (.block [.alu .cmp .esi (.imm 0)])

/-- The 114 rows, from 113 down to 0. -/
def combLoop : Prog isa := .seq (.block [.mov .esi (.imm 114)]) (.loop combStep .ne)

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
def scalarBase : Prog isa := .seq baseEntry (.seq combLoop baseEncode)

end VG.Impl.Ed448.X86
