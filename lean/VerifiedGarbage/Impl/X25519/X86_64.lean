import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Spec.X25519.Field64

/-!
# X25519: x86-64 implementation

`vg_x25519(out = rdi, scalar = rsi, point = rdx, scratch = rcx)`.

A field element is four 64-bit words `x0 + 2⁶⁴ x1 + 2¹²⁸ x2 + 2¹⁹² x3`,
any number below `2²⁵⁶`, standing for its residue modulo `p = 2²⁵⁵ - 19`;
only the result is reduced fully. Every element lives in the working space,
at a constant offset from its base, which is in `rdi` once the arguments are
read (`out` then in `rsi`):

* `[0, 48)`: the saved `rbx, rbp, r12–r15`;
* `x1, x2, z2, x3, z3` and the ladder's temporaries, 32 bytes each (`X1`, …);
* `swap` (a word, 0 or 1) and the bits of the clamped scalar `k` (`BITS`,
  byte `t` is bit `t` of `k`).

The arithmetic (registers `rax, rdx, rcx, rbp, r8–r15`), whose
multiplications (`mul`, `sqr`, and `mulSmallAdd` by `a24`) are the
`Field` `baseline`; the rest of the code takes them as a parameter
(`x25519With`), so that `vg_x25519_adx` (`X86_64/Adx.lean`) is this code with
other multiplications:

* `mul`: the 512-bit product, row by row (`r8–r15`, with the carry of a row
  in `rbp`), then `lo + 38 hi` (as `2²⁵⁶ ≡ 38`), whose carry word `c` is
  folded in as `38 c`, and a last carry of that as 38 more;
* `add`, `sub`: with carries (borrows), each carry folded in (subtracted) as
  38, twice; `addCmov` and `subCmov`, the ladder's, once, which is enough when an
  operand is at most `2p`, as products are;
* `sqr`: the products `a_i a_j` for `i < j` once, as rows of `mul`, then
  doubled, and the squares `a_i²` added; reduced as `mul`;
* `mulSmallAdd`: an element plus another by a one-word constant (`a24`),
  folded as for `mul`;
* `cswap`: with the mask `-swap`, as RFC 7748 §5 describes;
* `freeze`: the full reduction of the result, by folding bit 255 in as 19,
  then selecting `x + 19 - 2²⁵⁵` with a mask if it is not negative.

The ladder follows RFC 7748 §5 (in another order, `step`), over the bits of `k`
from 254 down to 0 (the counter `rbx`, which indexes `BITS`), and the
inversion `z2^(p-2)` is by Bernstein–Yang divsteps (`invertDS`), a call of
`vg_gf25519_r64_invert` (`invertCall`).

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

namespace VG.Impl.X25519.X86_64

open VG.X86_64

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `[rdi + d]`: byte `d` of the working space. -/
def sc (d : Nat) : MemOp := at_ .rdi d

/-! ## The layout of the working space -/

def X1 : Nat := 64
def X2 : Nat := 96
def Z2 : Nat := 128
def X3 : Nat := 160
def Z3 : Nat := 192
def A : Nat := 224
def B : Nat := 256
def C : Nat := 288
def D : Nat := 320
def AA : Nat := 352
def BB : Nat := 384
def E : Nat := 416
def DA : Nat := 448
def CB : Nat := 480
def T0 : Nat := 512
def T1 : Nat := 544
def T2 : Nat := 576
def T3 : Nat := 608
def SWAP : Nat := 640
def BITS : Nat := 768

/-- The words of a product, lowest first. -/
def T : List Reg := [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- `T[i]`. -/
def t (i : Nat) : Reg := T.getD i .r8

/-! ## Field arithmetic -/

/-- `t:c = t + c + ai · src` (a multiply-accumulate step; it never
overflows). -/
def mulStep (t c ai : Reg) (src : Src) : List Instr :=
  [.mov .rax src, .mul ai, .alu .add .rax (.reg c), .alu .adc .rdx (.imm 0),
    .alu .add t (.reg .rax), .alu .adc .rdx (.imm 0), .mov c (.reg .rdx)]

/-- `r8–r11 = 0`. -/
def zero4 : List Instr := [.mov32 .r8 (.imm 0), .mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0),
  .mov32 .r11 (.imm 0)]

/-- Row `i` of a product: `t[i..i+4] += a_i · b`, `a_i` from `[rdi + a + 8i]`,
`b` from `[rdi + b]`. -/
def row (a b i : Nat) : List Instr :=
  [.mov .rcx (.mem (sc (a + 8 * i))), .mov32 .rbp (.imm 0)] ++
    ((List.range 4).flatMap fun j => mulStep (t (i + j)) .rbp .rcx (.mem (sc (b + 8 * j)))) ++
    [.mov (t (i + 4)) (.reg .rbp)]

/-- `r8–r11 += rax`, with the carry out folded in as 38 (which cannot carry
again). -/
def carry38 : List Instr :=
  [.alu .add .r8 (.reg .rax), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
    .alu .adc .r11 (.imm 0), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38),
    .alu .add .r8 (.reg .rax)]

/-- `r8–r11 += rax`, for `rax < 2⁶³`, with bit 255 of `r8–r11` taken out and
added back as 19 (`2²⁵⁵ ≡ 19`), using `m` for the mask: the sum, below
`2²⁵⁵ + 2⁶⁴`, cannot carry out, so a product reduced this way is at most `2p`,
as `addL` and `subL` need. -/
def carry19 (m : Reg) : List Instr :=
  [.shift .shl .r11 1, .alu .sbb m (.reg m), .shift .shr .r11 1, .alu .and m (.imm 19),
    .alu .add .rax (.reg m), .alu .add .r8 (.reg .rax), .alu .adc .r9 (.imm 0),
    .alu .adc .r10 (.imm 0), .alu .adc .r11 (.imm 0)]

/-- `r8–r11 += 38 rbp`, with `rcx = 38`, at most `2p`. -/
def fold : List Instr := [.mov .rax (.reg .rbp), .mul .rcx] ++ carry19 .rbp

/-- `[rdi + o] = a, b, c, d`. -/
def stores (o : Nat) (a b c d : Reg) : List Instr :=
  [.store (sc o) a, .store (sc (o + 8)) b, .store (sc (o + 16)) c, .store (sc (o + 24)) d]

/-- `[rdi + o] = r8–r11`. -/
def store4 (o : Nat) : List Instr := stores o .r8 .r9 .r10 .r11

/-- `a, b, c, d = [rdi + o]`. -/
def loads (o : Nat) (a b c d : Reg) : List Instr :=
  [.mov a (.mem (sc o)), .mov b (.mem (sc (o + 8))), .mov c (.mem (sc (o + 16))),
    .mov d (.mem (sc (o + 24)))]

/-- `r8–r11 = r8–r11 + 38 r12–r15` with the carry word in `rbp`, folded. -/
def reduce : List Instr :=
  [.mov32 .rcx (.imm 38), .mov32 .rbp (.imm 0)] ++
    ((List.range 4).flatMap fun j => mulStep (t j) .rbp .rcx (.reg (t (4 + j)))) ++ fold

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`). -/
def mul (o a b : Nat) : List Instr :=
  zero4 ++ row a b 0 ++ row a b 1 ++ row a b 2 ++ row a b 3 ++ reduce ++ store4 o

/-- `r9–r12 = a₀ · (a₁, a₂, a₃)`, a row of `mul`. -/
def sq1 (a : Nat) : List Instr :=
  [.mov .rcx (.mem (sc a)), .mov32 .rbp (.imm 0), .mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0),
    .mov32 .r11 (.imm 0)] ++
    mulStep .r9 .rbp .rcx (.mem (sc (a + 8))) ++ mulStep .r10 .rbp .rcx (.mem (sc (a + 16))) ++
    mulStep .r11 .rbp .rcx (.mem (sc (a + 24))) ++ [.mov .r12 (.reg .rbp)]

/-- `r11–r13 = r11–r12 + a₁ · (a₂, a₃)`. -/
def sq2 (a : Nat) : List Instr :=
  [.mov .rcx (.mem (sc (a + 8))), .mov32 .rbp (.imm 0)] ++
    mulStep .r11 .rbp .rcx (.mem (sc (a + 16))) ++ mulStep .r12 .rbp .rcx (.mem (sc (a + 24))) ++
    [.mov .r13 (.reg .rbp)]

/-- `r13–r14 = r13 + a₂ a₃`. -/
def sq3 (a : Nat) : List Instr :=
  [.mov .rcx (.mem (sc (a + 16))), .mov32 .rbp (.imm 0)] ++
    mulStep .r13 .rbp .rcx (.mem (sc (a + 24))) ++ [.mov .r14 (.reg .rbp)]

/-- `r9–r15 = 2 · r9–r14`, and `r8 = rbp = 0`. -/
def sqDbl : List Instr :=
  [.mov32 .r15 (.imm 0), .mov32 .r8 (.imm 0), .alu .add .r9 (.reg .r9),
    .alu .adc .r10 (.reg .r10), .alu .adc .r11 (.reg .r11), .alu .adc .r12 (.reg .r12),
    .alu .adc .r13 (.reg .r13), .alu .adc .r14 (.reg .r14), .alu .adc .r15 (.reg .r15),
    .mov32 .rbp (.imm 0)]

/-- `t + 2⁶⁴ u + 2¹²⁸ rbp = t + 2⁶⁴ u + rbp + [d]²`: a square added at the
words `t`, `u`, the carry word `rbp` in and out. -/
def diag (t u : Reg) (d : Nat) : List Instr :=
  [.mov .rax (.mem (sc d)), .mul .rax, .alu .add .rax (.reg .rbp), .alu .adc .rdx (.imm 0),
    .alu .add t (.reg .rax), .alu .adc u (.reg .rdx), .mov32 .rbp (.imm 0),
    .alu .adc .rbp (.imm 0)]

/-- `[o] = [a]²`: the products `a_i a_j` (`i < j`) into `r9–r14` (by `a₀`,
then `a₁`, then `a₂`, as rows of `mul`), doubled into `r9–r15`, then the
squares `a_i²` added at `r8 + 2i` (`diag`), and reduced as in `mul`. -/
def sqr (o a : Nat) : List Instr :=
  sq1 a ++ sq2 a ++ sq3 a ++ sqDbl ++ diag .r8 .r9 a ++ diag .r10 .r11 (a + 8) ++
    diag .r12 .r13 (a + 16) ++ diag .r14 .r15 (a + 24) ++ reduce ++ store4 o

/-- `[o] = [b] + k · [a]`, for a constant `k < 2³¹`: `[b]` into `r8–r11`, then
`k · [a]` added word by word, and the carry word folded. -/
def mulSmallAdd (o b a : Nat) (k : BitVec 32) : List Instr :=
  loads b .r8 .r9 .r10 .r11 ++ [.mov32 .rcx (.imm k), .mov32 .rbp (.imm 0)] ++
    ((List.range 4).flatMap fun j => mulStep (t j) .rbp .rcx (.mem (sc (a + 8 * j)))) ++
    [.mov32 .rcx (.imm 38)] ++ fold ++ store4 o

/-- `[o] = [a] + [b]`. -/
def add (o a b : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
    .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++ carry38 ++ store4 o

/-- `[o] = [a] + [b]`, for `[a]` and `[b]` at most `2p`: the carry out folded in
once, as 38, which cannot carry again, since the sum is at most `4p`; the
result is at most `2p`. -/
def addL (o a b : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
    .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38),
    .alu .add .r8 (.reg .rax), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
    .alu .adc .r11 (.imm 0)] ++ store4 o

/-- `[o] = [a] - [b]`, for `[a]` and `[b]` at most `2p`: a borrow out
subtracted once, as 38, which cannot borrow again, since the difference is
then `[a] - [b] + 2p ≥ 0`; the result is at most `2p`. -/
def subL (o a b : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
    .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38),
    .alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
    .alu .sbb .r11 (.imm 0)] ++ store4 o

/-- `[o] = [a] + [b]`, for `[a]` or `[b]` at most `2p`, as `addL`, but with
the carry's 38 selected by `cmov` from a constant loaded before the sum: one
instruction after the carry rather than two, on a chain the ladder waits
for. `rcx` holds the zero `cmov` selects. -/
def addCmov (o a b : Nat) : List Instr :=
  [.alu32 .xor .rcx (.reg .rcx), .mov32 .rax (.imm 38),
    .mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
    .cmov .ae .rax (.reg .rcx),
    .alu .add .r8 (.reg .rax), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
    .alu .adc .r11 (.imm 0)] ++ store4 o

/-- `[o] = [a] - [b]`, for `[b]` at most `2p`, as `subL`, with the borrow's
38 selected by `cmov` as in `addCmov`. -/
def subCmov (o a b : Nat) : List Instr :=
  [.alu32 .xor .rcx (.reg .rcx), .mov32 .rax (.imm 38),
    .mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
    .cmov .ae .rax (.reg .rcx),
    .alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
    .alu .sbb .r11 (.imm 0)] ++ store4 o

/-- `[o] = [a] - [b]`: a borrow out is `2²⁵⁶ ≡ 38` too many, subtracted
(twice at most). -/
def sub (o a b : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
    .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38),
    .alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
    .alu .sbb .r11 (.imm 0), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38),
    .alu .sub .r8 (.reg .rax)] ++ store4 o

/-- Swaps `[x]` and `[y]` if the mask `rcx` is all ones (and not if it is
zero): both into `r8–r11` and `r12–r15`, then `d = rcx ∧ (x ⊕ y)`, `x ⊕= d`,
`y ⊕= d`, word by word (with `d` in `rax`), and both stored back. -/
def cswap (x y : Nat) : List Instr :=
  loads x .r8 .r9 .r10 .r11 ++ loads y .r12 .r13 .r14 .r15 ++
  ([(Reg.r8, Reg.r12), (.r9, .r13), (.r10, .r14), (.r11, .r15)].flatMap fun (a, b) =>
    [.mov .rax (.reg a), .alu .xor .rax (.reg b), .alu .and .rax (.reg .rcx),
      .alu .xor a (.reg .rax), .alu .xor b (.reg .rax)]) ++
  store4 x ++ stores y .r12 .r13 .r14 .r15

/-- The ladder's `a24 = 121665`. -/
def a24 : BitVec 32 := 121665

/-- The field multiplications, as each implementation of X25519 does them;
the rest of the code is the same for all. Both read the working space and
write `[o]` (which may be an operand), and use only the registers `rax`,
`rcx`, `rdx`, `rbp` and `r8–r15`. -/
structure Field where
  /-- `[o] = [a] · [b]` -/
  mul : Nat → Nat → Nat → List Instr
  /-- `[o] = [a]²` -/
  sqr : Nat → Nat → List Instr
  /-- `[o] = [b] + a24 · [a]` -/
  a24add : Nat → Nat → Nat → List Instr
  /-- `[o] = 2 · [a] · [b]` (Ed25519's doublings) -/
  mul2 : Nat → Nat → Nat → List Instr
  /-- `[o] = 2 · [a]²` (Ed25519's doublings) -/
  sqr2 : Nat → Nat → List Instr
  /-- The suffix of the functions built on these multiplications (`""` for the baseline's,
  `_adx` for BMI2 and ADX's). -/
  suffix : String := ""

/-- The baseline's: `mul`, `sqr` and `mulSmallAdd`, and a product doubled by `add`. -/
def baseline : Field where
  mul := mul
  sqr := sqr
  a24add o b a := mulSmallAdd o b a a24
  mul2 o a b := mul o a b ++ add o o o
  sqr2 o a := sqr o a ++ add o o o

/-- `[o] = [a]^(2^n)`, for `n ≥ 2`: a square, then `n - 1` in place. -/
def sqn (F : Field) (o a n : Nat) : Prog isa :=
  .seq (.block (F.sqr o a ++ [.mov32 .rbx (.imm (BitVec.ofNat 32 (n - 1)))]))
    (.loop (.block (F.sqr o o ++ [.alu .sub .rbx (.imm 1)])) .ne)

/-! ## The ladder -/

/-- One iteration of the ladder, for the bit `t = rbx - 1`: `k_t` from
`BITS`, `swap ^= k_t` into the mask `rcx = -swap`, the swaps, `swap = k_t`,
and the formulas of RFC 7748 §5, ordered by their dependencies rather than
as the RFC lists them: the four sums and differences, the four products of
them, and so on, so that independent multiplications are next to each other
and the processor overlaps them (the longest chain, to `z_3`, is three
multiplications). The sums and differences fold once (`addCmov`, `subCmov`): `z_2`
and `z_3` are products, at most `2p`, and so is an operand of each other sum
and the subtrahend of each other difference (`BB`, `CB`). `AA + a24 E` is one
multiply-add (`a24add`). -/
def step (F : Field) : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rax { base := .rdi, index := some .rbx, disp := BITS },
    .mov .rdx (.mem (sc SWAP)), .alu .xor .rdx (.reg .rax), .store (sc SWAP) .rax,
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] ++
  cswap X2 X3 ++ cswap Z2 Z3 ++
  addCmov A X2 Z2 ++ subCmov B X2 Z2 ++ addCmov C X3 Z3 ++ subCmov D X3 Z3 ++
  F.sqr AA A ++ F.sqr BB B ++ F.mul DA D A ++ F.mul CB C B ++
  subCmov E AA BB ++ subCmov Z3 DA CB ++ addCmov X3 DA CB ++ F.a24add Z2 AA E ++
  F.sqr Z3 Z3 ++ F.sqr X3 X3 ++ F.mul Z3 X1 Z3 ++
  F.mul X2 AA BB ++ F.mul Z2 E Z2 ++
  [.alu .test .rbx (.reg .rbx)]

/-- The 255 iterations, for `t` from 254 down to 0. -/
def ladder (F : Field) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 255)]) (.loop (.block (step F)) .ne)

/-- `[rdi + 8 rbx + BITS + j]`: bit `j` of byte `rbx` of the scalar. -/
def bitAt (j : Nat) : MemOp :=
  { base := .rdi, index := some .rbx, scale := 8, disp := ((BITS + j : Nat) : Int) }

/-- `BITS[8i + j] = bit j of scalar[i]`, for the 32 bytes `i` (the counter
`rbx`) of the scalar at `rsi`; then the clamped bits: `BITS[0..2] = 0` and
`BITS[254] = 1` (RFC 7748 §5, `decodeScalar25519`). -/
def bits : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 0)]) (.seq (.loop (.block (
    [.movzx8 .rax { base := .rsi, index := some .rbx }] ++
    ((List.range 8).flatMap fun j =>
      [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
      [.alu .and .rdx (.imm 1),
        .store8 (bitAt j) .rdx]) ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 32)])) .ne)
    (.block [.mov32 .rax (.imm 0), .store8 (sc BITS) .rax, .store8 (sc (BITS + 1)) .rax,
      .store8 (sc (BITS + 2)) .rax, .mov32 .rax (.imm 1), .store8 (sc (BITS + 254)) .rax]))

/-! ## Encoding and decoding -/

/-- `2⁶³ - 1`. -/
def low63 : BitVec 64 := 0x7fffffffffffffff

/-- The fully reduced `[a]` (`< p`) into `r8–r11`: bit 255 folded in as 19
(`x < 2²⁵⁵ + 19`), then `x + 19 - 2²⁵⁵` selected if it is not negative. -/
def freeze (a : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .mov .r9 (.mem (sc (a + 8))), .mov .r10 (.mem (sc (a + 16))),
    .mov .r11 (.mem (sc (a + 24))),
    .mov .rax (.reg .r11), .shift .shr .rax 63, .movImm64 .rdx low63, .alu .and .r11 (.reg .rdx),
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax), .alu .and .rcx (.imm 19),
    .alu .add .r8 (.reg .rcx), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
    .alu .adc .r11 (.imm 0),
    .mov .r12 (.reg .r8), .alu .add .r12 (.imm 19), .mov .r13 (.reg .r9), .alu .adc .r13 (.imm 0),
    .mov .r14 (.reg .r10), .alu .adc .r14 (.imm 0), .mov .r15 (.reg .r11),
    .alu .adc .r15 (.imm 0),
    .mov .rax (.reg .r15), .shift .shr .rax 63, .alu .and .r15 (.reg .rdx),
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax)] ++
  ([(Reg.r8, Reg.r12), (.r9, .r13), (.r10, .r14), (.r11, .r15)].flatMap fun (x, y) =>
    [.alu .xor y (.reg x), .alu .and y (.reg .rcx), .alu .xor x (.reg y)])

/-! ## Inversion by divsteps

`[T1] = [Z2]^(p-2)`, the inverse of `[Z2]` (zero for zero), by Bernstein–Yang
divsteps (`Proof/Divstep/`) in ten batches of 59: from `(d, f, g) = (1, p, x)`
for the fully reduced `x` and coefficients `(a, b) = (0, 1)`, a batch runs 59
divsteps on the low words of `f` and `g` (`dsteps`), giving the matrix
`(u, v, q, r)`, then `(f, g) := (u f + v g, q f + r g) / 2⁵⁹` exactly (`fRow`)
and `(a, b) := (u a + v b, q a + r b)` modulo `p` (`aRow`). Then `f = ±1` and
`± a ≡ x⁻¹ 2⁵⁹⁰`, so the result is `a` times `2⁻⁵⁹⁰` or `p - 2⁻⁵⁹⁰` by the
sign of `f`, one multiplication of `F`.

`f` and `g` are four words in two's complement, `a` and `b` four words below
`2²⁵⁶`. The working area is `[512, 768)`: `b`, `a` (the result's slot),
`f`, `g`, then `f'` (the constant at the end), `a'`, the words `d` and the
matrix, and the divsteps' low words of `f` and `g` and a temporary (`dsT`).
The count of batches is in `rbp` (times 256), and in `r14` during the
divsteps; it is public, as the branch on it is.

A batch's 59 divsteps run in packed chunks of `15, 15, 15, 14`, as the
short Weierstrass curves' (`Impl/Weierstrass/X86_64/Inv.lean`, whose code
this repeats under the names `pk…`, since that module imports this one): with
`P = [t] mod 2^15 + 2^31` and `Q = [t + 8] mod 2^15 + 2^47` (`pkSet`), the
rows `u P + v Q` and `q P + r Q` of the chunk's matrix, modulo `2^64`, in
`r8` and the `g` row's register, are updated as `(f, g)` would be, doubled
rather than halved (`pkStep`), so that step `j`'s parity is bit `j` of the
`g` row; their bits from 31 and 47 are `u` and `v` (`q` and `r`) plus
`2^14` once `2^30 + 2^45 + 2^61` is added (`pkExt`). `~d` is in `rbx`. Each
chunk's matrix updates the low words by `mul` (`pkLow`) and multiplies the
batch's so far in `r9`–`r12` (`pkComp`).

A product `m · X` of a signed word by four words is the unsigned product
`|m| · (X ^ s)` for the mask `s` of `m`'s sign: for `f` and `g`, plus
`|m|` if `m < 0` (as `-X = ~X + 1`) less `2²⁵⁶ |m|` if `X ^ s` is negative;
for `a` and `b`, less `37 |m|` if `m < 0` (as `~X = 2²⁵⁶ - 1 - X ≡ 37 - X`).
`a'` is the five-word sum `Q` less `37 c`, folded as `lo + 38 Q₄ - 37 c`
with the carry of that folded in as `±38`. -/

def dsB : Nat := 512
def dsA : Nat := 544
def dsF : Nat := 576
def dsG : Nat := 608
def dsNF : Nat := 640
def dsNA : Nat := 672
def dsK : Nat := 640
def dsD : Nat := 704
def dsU : Nat := 712
def dsV : Nat := 720
def dsQ : Nat := 728
def dsR : Nat := 736

/-- The divsteps' low words of `f` and `g`, and a temporary. -/
def dsT : Nat := 744

/-- Divstep `j` of a chunk: `~d` in `rbx`, the rows in `r8` and `g`, the next
`g` row into `t`. `g << (63 - j)` is `2^63` if `g` is odd and `0` if not (its
zero flag), and adding `~d` carries if `g` is odd and `d ≥ 0` (the swap):
`t` is `g`, `g + f`, or on a swap `g - f`, `f` becomes `g` on a swap and is
doubled, and `~d` becomes `~(2 - d)` on a swap and `~(d + 2)` if not. -/
def pkStep (j : Nat) (g t : Reg) : List Instr :=
  [.mov t (.reg g), .alu .add t (.reg .r8), .mov .rdx (.reg g), .alu .sub .rdx (.reg .r8),
    .mov .rcx (.imm (-2)), .alu .sub .rcx (.reg .rbx), .mov .rbp (.reg g), .shift .shl .rbp (63 - j),
    .cmov .e t (.reg g), .alu .add .rbp (.reg .rbx), .cmov .b t (.reg .rdx), .cmov .b .r8 (.reg g),
    .cmov .b .rbx (.reg .rcx), .alu .add .r8 (.reg .r8), .alu .sub .rbx (.imm 2)]

/-- The `g` row's register before step `j`: `r13` and `rax` in turn. -/
def pkReg (j : Nat) : Reg := if j % 2 = 0 then .r13 else .rax

/-- Steps `0 … n - 1`, the `g` row then moved back to `r13`. -/
def pkSteps (n : Nat) : List Instr :=
  (List.range n).flatMap (fun j => pkStep j (pkReg j) (pkReg (j + 1))) ++
    (if n % 2 = 1 then [.mov .r13 (.reg .rax)] else [])

/-- A row's start: `r = [t] mod 2^15 + c`, through `rax`. -/
def pkSetRow (r : Reg) (t : Nat) (c : BitVec 64) : List Instr :=
  [.mov r (.mem (sc t)), .alu .and r (.imm 0x7fff), .movImm64 .rax c, .alu .add r (.reg .rax)]

/-- The rows' start: `r8 = [t] mod 2^15 + 2^31`, `r13 = [t + 8] mod 2^15 + 2^47`. -/
def pkSet (t : Nat) : List Instr := pkSetRow .r8 t (2 ^ 31) ++ pkSetRow .r13 (t + 8) (2 ^ 47)

/-- What makes the rows' fields nonnegative: `2^30` below bit 31, `2^14` at bits 31 and 47. -/
def pkExtC : BitVec 64 := 2 ^ 30 + 2 ^ 45 + 2 ^ 61

/-- The matrix `u, v, q, r` into `r8`, `rcx`, `r13`, `rbp`, from the rows in `r8`, `r13`. -/
def pkExt : List Instr :=
  [.movImm64 .rcx pkExtC, .alu .add .r8 (.reg .rcx), .alu .add .r13 (.reg .rcx),
    .mov .rcx (.reg .r8), .shift .shr .rcx 47, .alu .sub .rcx (.imm 16384),
    .shift .shl .r8 17, .shift .shr .r8 48, .alu .sub .r8 (.imm 16384),
    .mov .rbp (.reg .r13), .shift .shr .rbp 47, .alu .sub .rbp (.imm 16384),
    .shift .shl .r13 17, .shift .shr .r13 48, .alu .sub .r13 (.imm 16384)]

/-- `rax = [d] r` (the low word of the product), through `rdx`. -/
def pkLdMul (d : Nat) (r : Reg) : List Instr := [.mov .rax (.mem (sc d)), .mul r]

/-- `[e] = (rax + [d]) >> n`. -/
def pkAddShr (d n e : Nat) : List Instr :=
  [.alu .add .rax (.mem (sc d)), .shift .shr .rax n] ++ [.store (sc e) .rax]

/-- `[t] = (u [t] + v [t + 8]) >> n`, `[t + 8] = (q [t] + r [t + 8]) >> n`
(modulo `2^64`), through `rax`, `rdx` and `[t + 16]`. -/
def pkLow (n t : Nat) : List Instr :=
  pkLdMul t .r8 ++ [.store (sc (t + 16)) .rax] ++ pkLdMul (t + 8) .rcx ++ pkAddShr (t + 16) n (t + 16) ++
    pkLdMul t .r13 ++ [.store (sc t) .rax] ++ pkLdMul (t + 8) .rbp ++ pkAddShr t n (t + 8) ++
    [.mov .rax (.mem (sc (t + 16))), .store (sc t) .rax]

/-- The first chunk's matrix is the batch's so far. -/
def pkFirst : List Instr :=
  [.mov .r9 (.reg .r8), .mov .r10 (.reg .rcx), .mov .r11 (.reg .r13), .mov .r12 (.reg .rbp)]

/-- A column `(x, y)` of the batch's matrix, times the chunk's: `x = u x + v y`
and `y = q x + r y`, through `rax`, `rdx` and `[t]`. -/
def pkCol (x y : Reg) (t : Nat) : List Instr :=
  [.mov .rax (.reg .r13), .mul x, .store (sc t) .rax] ++
    [.mov .rax (.reg .r8), .mul x, .mov x (.reg .rax), .mov .rax (.reg .rcx), .mul y, .alu .add x (.reg .rax),
      .mov .rax (.reg .rbp), .mul y] ++
    [.alu .add .rax (.mem (sc t)), .mov y (.reg .rax)]

/-- The batch's matrix times the chunk's. -/
def pkComp (t : Nat) : List Instr := pkCol .r9 .r11 t ++ pkCol .r10 .r12 t

/-- A chunk of `n` steps, from the low words at `[t]`, `[t + 8]`: the low
words updated unless it is the last, and the matrix the batch's if it is
the first. -/
def pkChunk (t n : Nat) (first last : Bool) : List Instr :=
  pkSet t ++ pkSteps n ++ pkExt ++ (if last then [] else pkLow n t) ++ (if first then pkFirst else pkComp (t + 16))

/-- A batch's start: the count of batches into `r14`, the low words of `f`
and `g` into `[dsT]`, `[dsT + 8]`, and `~d` into `rbx`. -/
def dstart : List Instr :=
  [.mov .r14 (.reg .rbp), .mov .rax (.mem (sc dsF)), .store (sc dsT) .rax, .mov .rax (.mem (sc dsG)),
    .store (sc (dsT + 8)) .rax, .mov .rbx (.mem (sc dsD)), .alu .xor .rbx (.imm (-1))]

/-- 59 divsteps in chunks of `15, 15, 15, 14`; then `d` and the matrix
stored, and the count of batches back in `rbp`. -/
def dsteps : Prog isa :=
  .block (dstart ++ pkChunk dsT 15 true false ++ pkChunk dsT 15 false false ++ pkChunk dsT 15 false false ++
    pkChunk dsT 14 false true ++
    [.alu .xor .rbx (.imm (-1)), .store (sc dsD) .rbx, .store (sc dsU) .r9, .store (sc dsV) .r10,
      .store (sc dsQ) .r11, .store (sc dsR) .r12, .mov .rbp (.reg .r14)])

/-- `r15` = the mask of `[m]`'s sign, `r14 = |[m]|`, through `rax` and `rcx`. -/
def absM (m : Nat) : List Instr :=
  [.mov .rcx (.mem (sc m)), .mov .r15 (.reg .rcx), .shift .shr .r15 63, .mov32 .rax (.imm 0),
    .alu .sub .rax (.reg .r15), .mov .r15 (.reg .rax), .mov .r14 (.reg .rcx), .alu .xor .r14 (.reg .r15),
    .alu .sub .r14 (.reg .r15)]

/-- `t:c = t + c + ai · (src ^ k)`. -/
def mulStepX (t c ai k : Reg) (src : Src) : List Instr :=
  [.mov .rax src, .alu .xor .rax (.reg k)] ++ (mulStep t c ai (.reg .rax)).tail

/-- `r8–r12 += r14 · ([x] ^ r15)` (modulo `2³²⁰`), the carries in `r13`. -/
def dsRow (x : Nat) : List Instr :=
  [.mov32 .r13 (.imm 0)] ++ mulStepX .r8 .r13 .r14 .r15 (.mem (sc x)) ++
    mulStepX .r9 .r13 .r14 .r15 (.mem (sc (x + 8))) ++ mulStepX .r10 .r13 .r14 .r15 (.mem (sc (x + 16))) ++
    mulStepX .r11 .r13 .r14 .r15 (.mem (sc (x + 24))) ++ [.alu .add .r12 (.reg .r13)]

/-- `r12 -= r14` if `[x + 24] ^ r15` is negative. -/
def topCorr (x : Nat) : List Instr :=
  [.mov .rax (.mem (sc (x + 24))), .alu .xor .rax (.reg .r15), .shift .shr .rax 63, .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .alu .and .rdx (.reg .r14), .alu .sub .r12 (.reg .rdx)]

/-- `rbx += r14 & r15`: `|m|` if `m < 0`. -/
def cAcc : List Instr := [.mov .rax (.reg .r14), .alu .and .rax (.reg .r15), .alu .add .rbx (.reg .rax)]

/-- `r8–r12 = 0`, `rbx = 0`. -/
def zeroP : List Instr :=
  [.mov32 .r8 (.imm 0), .mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0),
    .mov32 .r12 (.imm 0), .mov32 .rbx (.imm 0)]

/-- `r8–r12 += |m| · ([x] ^ s)`, `rbx += |m|` if `m < 0`, and for a signed `[x]` the
correction of its top word. -/
def prod (m x : Nat) (signed : Bool) : List Instr :=
  absM m ++ dsRow x ++ (if signed then topCorr x else []) ++ cAcc

/-- `[dst] = ([m₁] [f] + [m₂] [g]) / 2⁵⁹`: the five words plus `rbx`, then
shifted. -/
def fRow (m₁ m₂ dst : Nat) : List Instr :=
  zeroP ++ prod m₁ dsF true ++ prod m₂ dsG true ++
  [.alu .add .r8 (.reg .rbx), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0), .alu .adc .r11 (.imm 0),
    .alu .adc .r12 (.imm 0)] ++
  ([(Reg.r8, Reg.r9, 0), (.r9, .r10, 8), (.r10, .r11, 16), (.r11, .r12, 24)].flatMap fun (lo, hi, d) =>
    [.mov .rax (.reg lo), .shift .shr .rax 59, .mov .rdx (.reg hi), .shift .shl .rdx 5,
      .alu .add .rax (.reg .rdx), .store (sc (dst + d)) .rax])

/-- `r8–r11 = r8–r12 - 37 rbx` modulo `p`, below `2²⁵⁶`: `lo + w` for
`w = 38 r12 - 37 rbx` (two words, signed), then its carry as `±38`. -/
def foldP : List Instr :=
  [.mov32 .rax (.imm 38), .mul .r12, .mov .r13 (.reg .rax), .mov .r14 (.reg .rdx),
    .mov32 .rax (.imm 37), .mul .rbx, .alu .sub .r13 (.reg .rax), .alu .sbb .r14 (.reg .rdx),
    .mov .r15 (.reg .r14), .shift .shr .r15 63, .mov32 .rax (.imm 0), .alu .sub .rax (.reg .r15),
    .alu .add .r8 (.reg .r13), .alu .adc .r9 (.reg .r14), .alu .adc .r10 (.reg .rax), .alu .adc .r11 (.reg .rax),
    .alu .sbb .rdx (.reg .rdx), .alu .and .rdx (.imm 38), .alu .and .rax (.imm 38), .alu .sub .rdx (.reg .rax),
    .mov .r15 (.reg .rdx), .shift .shr .r15 63, .mov32 .rax (.imm 0), .alu .sub .rax (.reg .r15),
    .alu .add .r8 (.reg .rdx), .alu .adc .r9 (.reg .rax), .alu .adc .r10 (.reg .rax), .alu .adc .r11 (.reg .rax)]

/-- `[dst] = [m₁] [a] + [m₂] [b]` modulo `p`, below `2²⁵⁶`. -/
def aRow (m₁ m₂ dst : Nat) : List Instr :=
  zeroP ++ prod m₁ dsA false ++ prod m₂ dsB false ++ foldP ++ store4 dst

/-- `[dst] = [src]` (four words), through `r8–r11`. -/
def copy4 (dst src : Nat) : List Instr := loads src .r8 .r9 .r10 .r11 ++ store4 dst

/-- The count of batches (times 256, in `rbp`) less one, its zero flag for the loop. -/
def batchEnd : List Instr := [.alu .sub .rbp (.imm 256)]

/-- A batch. -/
def dbatch : Prog isa :=
  .seq dsteps (.block (fRow dsU dsV dsNF ++ fRow dsQ dsR dsG ++ copy4 dsF dsNF ++
    aRow dsU dsV dsNA ++ aRow dsQ dsR dsB ++ copy4 dsA dsNA ++ batchEnd))

/-- `2⁻⁵⁹⁰ mod p`. -/
def kInv : Nat := 0x276508b2417706156c6c893805ac5242a8c68f3f1d132595a0f99e2375022099

/-- `p - 2⁻⁵⁹⁰ mod p`. -/
def kInvNeg : Nat := 0x589af74dbe88f9ea939376c7fa53adbd573970c0e2ecda6a5f0661dc8afddf54

/-- `p`. -/
def pNat : Nat := 2 ^ 255 - 19

/-- The start: `g = x` fully reduced, `f = p`, `a = 0`, `b = 1`, `d = 1`, and
ten batches. -/
def dinit : List Instr :=
  freeze Z2 ++ store4 dsG ++
  ((List.range 4).flatMap fun i =>
    [.movImm64 .rax (BitVec.ofNat 64 (pNat >>> (64 * i))), .store (sc (dsF + 8 * i)) .rax]) ++
  [.mov32 .rax (.imm 0)] ++ stores dsA .rax .rax .rax .rax ++ stores dsB .rax .rax .rax .rax ++
  [.mov32 .rax (.imm 1), .store (sc dsB) .rax, .store (sc dsD) .rax, .mov32 .rbp (.imm 2560)]

/-- `[dsK] = 2⁻⁵⁹⁰` if `f ≥ 0`, else `p - 2⁻⁵⁹⁰`. -/
def dsel : List Instr :=
  [.mov .rdx (.mem (sc (dsF + 24))), .shift .shr .rdx 63, .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] ++
  ((List.range 4).flatMap fun i =>
    [.movImm64 .rax (BitVec.ofNat 64 (kInv >>> (64 * i))), .movImm64 .rdx (BitVec.ofNat 64 (kInvNeg >>> (64 * i))),
      .alu .xor .rdx (.reg .rax), .alu .and .rdx (.reg .rcx), .alu .xor .rax (.reg .rdx),
      .store (sc (dsK + 8 * i)) .rax])

/-- `[T1] = [Z2]^(p-2)`, by divsteps. -/
def invertDS (F : Field) : Prog isa :=
  .seq (.block dinit) (.seq (.loop dbatch .ne) (.block (dsel ++ F.mul T1 T1 dsK)))

/-- The callee-saved registers the inversion writes, into `xmm0`–`xmm5`. -/
def invSaves : List Instr :=
  [.xop (.movq .xmm0 .rbx), .xop (.movq .xmm1 .rbp), .xop (.movq .xmm2 .r12),
    .xop (.movq .xmm3 .r13), .xop (.movq .xmm4 .r14), .xop (.movq .xmm5 .r15)]

/-- The callee-saved registers back from `xmm0`–`xmm5`. -/
def invRestores : List Instr :=
  [.movqR .rbx .xmm0, .movqR .rbp .xmm1, .movqR .r12 .xmm2, .movqR .r13 .xmm3, .movqR .r14 .xmm4,
    .movqR .r15 .xmm5]

/-- `vg_gf25519_r64_invert(ws = rdi)`: `[T1] = [Z2]^(p-2)` by divsteps, with the
baseline multiplication, the callee-saved registers kept in `xmm0`–`xmm5`. -/
def invertFn : Prog isa := .seq (.block invSaves) (.seq (invertDS baseline) (.block invRestores))

/-- A call of `vg_gf25519_r64_invert`, which every inversion of the x86-64 code
is (`ws` in `rdi`). -/
def invertCall : Prog isa := .call Spec.X25519.Field64.invertApi.name invertFn

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 0), (.rbp, 8), (.r12, 16), (.r13, 24), (.r14, 32), (.r15, 40)]

/-- Saves them (with the working space in `rcx`). -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .rcx d) r

def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (sc d))

/-- The u-coordinate at `rdx`, its top bit masked, into `r8–r11`. -/
def loadU : List Instr :=
  [.mov .r8 (.mem (at_ .rdx 0)), .mov .r9 (.mem (at_ .rdx 8)), .mov .r10 (.mem (at_ .rdx 16)),
    .mov .r11 (.mem (at_ .rdx 24)), .movImm64 .rax low63, .alu .and .r11 (.reg .rax)]

/-- Reads the arguments (with the working space in `rcx`): `u` with its top
bit masked into `X1` and `X3`; then `out` into `r12`, the working space into
`rdi`, and `x2 = 1`, `z2 = 0`, `z3 = 1`, `swap = 0`. The scalar stays at
`rsi` for `bits`. -/
def setup : List Instr :=
  loadU ++ save ++ [.mov .r12 (.reg .rdi), .mov .rdi (.reg .rcx)] ++ store4 X1 ++ store4 X3 ++
    [.mov32 .rax (.imm 0), .mov32 .rdx (.imm 1)] ++ stores X2 .rdx .rax .rax .rax ++
    stores Z2 .rax .rax .rax .rax ++ stores Z3 .rdx .rax .rax .rax ++ [.store (sc SWAP) .rax]

/-- `x2 · z2^(p-2)`, reduced fully, to `out`, and the saved registers
restored (before the stores, which do not touch the working space). -/
def finish (F : Field) : List Instr :=
  F.mul X2 X2 T1 ++ freeze X2 ++ restore ++
  [.store (at_ .rsi 0) .r8, .store (at_ .rsi 8) .r9, .store (at_ .rsi 16) .r10,
    .store (at_ .rsi 24) .r11]

/-- The swap after the loop. -/
def lastSwap : List Instr :=
  [.mov .rdx (.mem (sc SWAP)), .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] ++
  cswap X2 X3 ++ cswap Z2 Z3

/-- X25519 with the ladder `lad` (which leaves the ladder's final state in the
working space as `ladder` does) and the field multiplications `F` for the
inversion. -/
def x25519Of (F : Field) (lad : Prog isa) : Prog isa :=
  .seq (.block setup) <| .seq bits <| .seq (.block [.mov .rsi (.reg .r12)]) <| .seq lad <|
    .seq (.block lastSwap) <| .seq invertCall (.block (finish F))

/-- X25519 with the field multiplications `F`. -/
def x25519With (F : Field) : Prog isa := x25519Of F (ladder F)

def x25519 : Prog isa := x25519With baseline

end VG.Impl.X25519.X86_64
