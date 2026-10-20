module

public import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant
public import VerifiedGarbage.Impl.Ed448.X86_64.Scalar
public import VerifiedGarbage.Impl.Ed448.Comb

/-!
# Ed448 base-point multiplication on x86-64

`vg_ed448_scalar_base(out = rdi, scalar = rsi, scratch = rdx)`: the encoding
of `[s]B` for the 456-bit little-endian scalar `s`, without pruning.

Field elements are X448's (seven 64-bit words in the slots of the working
space, `Impl/X448/X86_64.lean`), and so is the field arithmetic: the field
multiplications `F` (the baseline's or BMI2 and ADX's), additions,
subtractions, the constant-time swap, the inversion and the full reduction.
Points are the specification's projective coordinates `(X : Y : Z)`.

The scalar's bits are expanded into bytes at `BITS` (byte `t` is bit `t`),
as X448 expands its scalar. A four-column comb groups bits separated by 114
positions, processing 114 rows from high to low. Each row doubles `R`
(slots 0–2), selects one of 16 precomputed affine points with a full masked
table scan, and adds it to `R`. The table covers all 456 input bits,
including the eight bits that signing's reduced scalars leave clear.
The doubling and the
addition are calls of `vg_ed448_r64_point_double` and
`vg_ed448_r64_point_add_affine` (`Point64.lean`), which keep `rsi` and
`rbx`: the output's address is kept in `rsi` across the loop, and stored
again at `OUT` after it, since a taint analysis forgets the working space's
public words at a call. Finally `R` is encoded
(§5.2.2): `Z` inverted, `x = X/Z` and `y = Y/Z` fully reduced, and the low
bit of `x` stored as the top bit of the 57th byte.

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Ed448.X86_64

open VG.X86_64
open VG.Impl.X448.X86_64 (at_ sc W w loads stores slot Field add sub cswap freeze invert invertCall BITS bitAt)

/-! ## Constants -/

/-- The seven 64-bit words of `v`, lowest first. -/
def words7 (v : Nat) : List (BitVec 64) := (List.range 7).map fun i => BitVec.ofNat 64 (v >>> (64 * i))

/-- The field element `v` into slot `i`. -/
def constSlot (i : Nat) (v : Spec.X448.Fe) : List Instr :=
  (W.zip (words7 v.val)).map (fun (r, x) => .movImm64 r x) ++ stores (slot i) W

/-- `R` the neutral point `(0 : 1 : 1)`, `Q` the base point `(X : Y : 1)`, and
`d`. -/
def consts : List Instr :=
  constSlot 0 0 ++ constSlot 1 1 ++ constSlot 2 1 ++ constSlot 8 Spec.Ed448.basePoint.X ++
    constSlot 9 Spec.Ed448.basePoint.Y ++ constSlot 10 1 ++ constSlot 11 Spec.Ed448.d

/-! ## The scalar's bits -/

/-- The body of the loop over the scalar's 57 bytes (the counter `rbx`):
bit `j` of byte `rbx` at `BITS + 8 rbx + j`. -/
def bitsBody : List Instr :=
  [.movzx8 .rax { base := .rsi, index := some .rbx }] ++
    ((List.range 8).flatMap fun j =>
      [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
      [.alu .and .rdx (.imm 1), .store8 (bitAt j) .rdx]) ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 57)]

def bits : Prog isa := .seq (.block [.mov32 .rbx (.imm 0)]) (.loop (.block bitsBody) .ne)

/-! ## The loop over the bits -/

/-- `rcx = -BITS[rbx]`: the mask of bit `rbx`. -/
def bitMask : List Instr :=
  [.movzx8 .rdx { base := .rdi, index := some .rbx, disp := (BITS : Int) }, .mov32 .rcx (.imm 0),
    .alu .sub .rcx (.reg .rdx)]

/-- `T` swapped into `R` by the mask of bit `rbx`, and ZF set at the last bit. -/
def stepSwap : List Instr :=
  bitMask ++ cswap (slot 0) (slot 3) ++ cswap (slot 1) (slot 4) ++ cswap (slot 2) (slot 5) ++
    [.alu .test .rbx (.reg .rbx)]

/-- One bit `t = rbx - 1`, from the top: `R = 2R`, `T = R + B`, and `T`
swapped into `R` if bit `t` is set, with the point operations `P`. -/
def step (P : Point64.Ops) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <| .seq P.dbl <| .seq P.add (.block stepSwap)

/-- The 456 bits, from 455 down to 0. -/
def mulLoop (P : Point64.Ops) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 456)]) (.loop (step P) .ne)

/-! ## Four-column fixed-base comb -/

/-- The mask of `i` matching bits `rbx + {0,114,228,342}` of the scalar.
All four addresses depend only on the public loop counter. -/
def combMask (i : Nat) : List Instr :=
  [.movzx8 .rax { base := .rdi, index := some .rbx, disp := ((BITS + 342 : Nat) : Int) },
   .movzx8 .rdx { base := .rdi, index := some .rbx, disp := ((BITS + 228 : Nat) : Int) },
   .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rdx),
   .movzx8 .rdx { base := .rdi, index := some .rbx, disp := ((BITS + 114 : Nat) : Int) },
   .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rdx),
   .movzx8 .rdx { base := .rdi, index := some .rbx, disp := BITS },
   .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rdx),
   .alu .xor .rax (.imm (BitVec.ofNat 32 i)), .alu .cmp .rax (.imm 1),
   .mov32 .rcx (.imm 0), .alu .sbb .rcx (.reg .rcx)]

/-- Read one literal table entry and conditionally select it into slots 8–9.
The entry is materialized regardless of the secret index. -/
def combEntry (i : Nat) : List Instr :=
  constSlot 3 (Comb.entry i).1 ++ constSlot 4 (Comb.entry i).2 ++ combMask i ++
    cswap (slot 8) (slot 3) ++ cswap (slot 9) (slot 4)

/-- Select an affine comb point by scanning every entry, including the identity. -/
def combSelect : List Instr := (List.range 16).flatMap combEntry

/-- Replace the accumulator by the sum in slots 3–5. -/
def combAccept : List Instr :=
  Impl.X448.X86_64.copyOut (slot 0) (slot 3) ++
  Impl.X448.X86_64.copyOut (slot 1) (slot 4) ++
  Impl.X448.X86_64.copyOut (slot 2) (slot 5) ++ [.alu .test .rbx (.reg .rbx)]

def combStep (P : Point64.Ops) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <| .seq P.dbl <|
  .seq (.block combSelect) <| .seq P.add (.block combAccept)

/-- 114 iterations, processing all 456 bits with four columns. -/
def combLoop (P : Point64.Ops) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 114)]) (.loop (combStep P) .ne)

/-! ## Entry and exit -/

/-- The callee-saved registers saved at the working space `rdx`, the output's
address into `r15`, the working space into `rdi`, and the constants. -/
def entry : List Instr :=
  saveAt .rdx ++ ([.mov .r15 (.reg .rdi), .mov .rdi (.reg .rdx)] ++ consts)

/-- The output's address at `OUT`, once the scalar's bits are stored (a store
of a secret at an address with a counter, as the bits are, would leave the
taint analysis unable to tell that `OUT` holds a public value), and in `rsi`,
which the loop keeps. -/
def stashOut : List Instr := [.store (at_ .rdi OUT) .r15, .mov .rsi (.reg .r15)]

/-- The output's address at `OUT` again, from `rsi`, after the loop's calls. -/
def restashOut : List Instr := [.store (at_ .rdi OUT) .rsi]

/-- `rsi = 128 · (r8 mod 2)`: the top bit of the encoding's last byte, from
the low bit of `x`. -/
def signBit : List Instr := [.mov .rsi (.reg .r8), .alu .and .rsi (.imm 1), .shift .ror .rsi 57]

/-- `x = X/Z` into slot 3 and `y = Y/Z` into slot 4, with `1/Z` in slot 21
(the inversion's result); `x` fully reduced and its low bit kept in `rsi`;
`y` fully reduced to the output's first 56 bytes, and the low bit of `x` as
the top bit of its 57th; then the callee-saved registers restored. The
output's address is read from `OUT` once, before any store to the output
(after which the taint analysis no longer knows `OUT` to be public). -/
def encode (F : Field) : List Instr :=
  F.mul (slot 3) (slot 0) (slot 21) ++ (F.mul (slot 4) (slot 1) (slot 21) ++ (freeze (slot 3) ++
    (signBit ++ (freeze (slot 4) ++ ([.mov .rax (.mem (sc OUT))] ++
    ((List.range 7).map (fun i => .store (at_ .rax (8 * i)) (w i)) ++
    ([.store8 (at_ .rax 56) .rsi] ++ Impl.X448.X86_64.restore)))))))

/-- `vg_ed448_scalar_base` with the field multiplications `F`, the point operations `P` and
the inversion `inv` (`invert F`, or `invertCall F`, which calls `vg_gf448_r64_pow223`). -/
def scalarBaseWith (F : Field) (P : Point64.Ops) (inv : Prog isa := invert F) : Prog isa :=
  .seq (.block entry) <| .seq bits <| .seq (.block stashOut) <| .seq (combLoop P) <|
    .seq (.block restashOut) <| .seq inv (.block (encode F))

/-- The point operations call `vg_ed448_r64_point_double` and `vg_ed448_r64_point_add_affine`,
and the inversion `vg_gf448_r64_pow223`, keeping the output's address at `OUT`. -/
def scalarBaseFor (v : FieldVariant) : Prog isa :=
  scalarBaseWith v.field v.calls (Impl.X448.X86_64.invertCallWith v.field v.powName [OUT])

def scalarBase : Prog isa := scalarBaseFor .scalar
def scalarBaseAdx : Prog isa := scalarBaseFor .adx

end VG.Impl.Ed448.X86_64
