import VerifiedGarbage.TCB.X86_64.Isa

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
multiplications (`mul`, `sqr`, and `mulSmall` by `a24`) are the
`Field` `baseline`; the rest of the code takes them as a parameter
(`x25519With`), so that `vg_x25519_adx` (`X86_64/Adx.lean`) is this code with
other multiplications:

* `mul`: the 512-bit product, row by row (`r8–r15`, with the carry of a row
  in `rbp`), then `lo + 38 hi` (as `2²⁵⁶ ≡ 38`), whose carry word `c` is
  folded in as `38 c`, and a last carry of that as 38 more;
* `add`, `sub`: with carries (borrows), each carry folded in (subtracted) as
  38, twice;
* `sqr`: the products `a_i a_j` for `i < j` once, as rows of `mul`, then
  doubled, and the squares `a_i²` added; reduced as `mul`;
* `mulSmall`: by a one-word constant (`a24`), folded as for `mul`;
* `cswap`: with the mask `-swap`, as RFC 7748 §5 describes;
* `freeze`: the full reduction of the result, by folding bit 255 in as 19,
  then selecting `x + 19 - 2²⁵⁵` with a mask if it is not negative.

The ladder follows RFC 7748 §5 (in another order, `step`), over the bits of `k`
from 254 down to 0 (the counter `rbx`, which indexes `BITS`), and the
inversion `z2^(p-2)` is by Bernstein–Yang divsteps (`invertDS`).

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

/-- `r8–r11 += 38 rbp`, with `rcx = 38`. -/
def fold : List Instr := [.mov .rax (.reg .rbp), .mul .rcx] ++ carry38

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

/-- `[o] = k · [a]`, for a constant `k < 2³¹`. -/
def mulSmall (o a : Nat) (k : BitVec 32) : List Instr :=
  zero4 ++ [.mov32 .rcx (.imm k), .mov32 .rbp (.imm 0)] ++
    ((List.range 4).flatMap fun j => mulStep (t j) .rbp .rcx (.mem (sc (a + 8 * j)))) ++
    [.mov32 .rcx (.imm 38)] ++ fold ++ store4 o

/-- `[o] = [a] + [b]`. -/
def add (o a b : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
    .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++ carry38 ++ store4 o

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
  /-- `[o] = a24 · [a]` -/
  a24 : Nat → Nat → List Instr
  /-- `[o] = 2 · [a] · [b]` (Ed25519's doublings) -/
  mul2 : Nat → Nat → Nat → List Instr
  /-- `[o] = 2 · [a]²` (Ed25519's doublings) -/
  sqr2 : Nat → Nat → List Instr

/-- The baseline's: `mul`, `sqr` and `mulSmall`, and a product doubled by `add`. -/
def baseline : Field where
  mul := mul
  sqr := sqr
  a24 o a := mulSmall o a a24
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
multiplications). -/
def step (F : Field) : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rax { base := .rdi, index := some .rbx, disp := BITS },
    .mov .rdx (.mem (sc SWAP)), .alu .xor .rdx (.reg .rax), .store (sc SWAP) .rax,
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] ++
  cswap X2 X3 ++ cswap Z2 Z3 ++
  add A X2 Z2 ++ sub B X2 Z2 ++ add C X3 Z3 ++ sub D X3 Z3 ++
  F.sqr AA A ++ F.sqr BB B ++ F.mul DA D A ++ F.mul CB C B ++
  sub E AA BB ++ sub Z3 DA CB ++ add X3 DA CB ++ F.a24 Z2 E ++
  F.sqr Z3 Z3 ++ F.sqr X3 X3 ++ add Z2 AA Z2 ++ F.mul Z3 X1 Z3 ++
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
divsteps on the low words of `f` and `g` (`dstep`), giving the matrix
`(u, v, q, r)`, then `(f, g) := (u f + v g, q f + r g) / 2⁵⁹` exactly (`fRow`)
and `(a, b) := (u a + v b, q a + r b)` modulo `p` (`aRow`). Then `f = ±1` and
`± a ≡ x⁻¹ 2⁵⁹⁰`, so the result is `a` times `2⁻⁵⁹⁰` or `p - 2⁻⁵⁹⁰` by the
sign of `f`, one multiplication of `F`.

`f` and `g` are four words in two's complement, `a` and `b` four words below
`2²⁵⁶`. The working area is `[512, 768)`: `b`, `a` (the result's slot),
`f`, `g`, then `f'` (the constant at the end), `a'`, and the words `d` and the matrix.
The count of batches is in `rbp` (times 256) but during the divsteps, when it is
above the count of steps in `r8`: both are public, as the branches on them are.

A divstep keeps `d`, `f`, `g`, `u`, `v`, `q`, `r` in `rbx`, `rcx`, `rbp`,
`r9`–`r12` and `d > 0` (0 or 1) in `r13`: with `rax` and `rdx`, the
candidates `g + f` and `g - f` are selected by `cmov` on the flags of
`g & (d > 0)` (the swap) and `g & 1` (`g` odd), and so on for the matrix
with `g` and the old `d > 0` kept in `r14` and `r15`; the steps are counted
in `r8`.

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

/-- One divstep on words. -/
def dstep : List Instr :=
  [.mov32 .rax (.imm 2), .alu .sub .rax (.reg .rbx), .alu .add .rbx (.imm 2),
    .alu .test .rbp (.reg .r13), .cmov .ne .rbx (.reg .rax),
    .mov .rax (.reg .rbp), .alu .add .rax (.reg .rcx), .mov .rdx (.reg .rbp), .alu .sub .rdx (.reg .rcx),
    .alu .test .rbp (.reg .r13), .cmov .ne .rax (.reg .rdx), .cmov .ne .rcx (.reg .rbp),
    .alu .test .rbp (.imm 1), .mov .r14 (.reg .rbp), .cmov .ne .rbp (.reg .rax), .shift .shr .rbp 1,
    .mov .r15 (.reg .r13), .mov .r13 (.reg .rbx), .shift .shr .r13 63, .alu .xor .r13 (.imm 1),
    .mov .rax (.reg .r11), .alu .add .rax (.reg .r9), .mov .rdx (.reg .r11), .alu .sub .rdx (.reg .r9),
    .alu .test .r14 (.reg .r15), .cmov .ne .rax (.reg .rdx), .cmov .ne .r9 (.reg .r11),
    .alu .test .r14 (.imm 1), .cmov .ne .r11 (.reg .rax),
    .mov .rax (.reg .r12), .alu .add .rax (.reg .r10), .mov .rdx (.reg .r12), .alu .sub .rdx (.reg .r10),
    .alu .test .r14 (.reg .r15), .cmov .ne .rax (.reg .rdx), .cmov .ne .r10 (.reg .r12),
    .alu .test .r14 (.imm 1), .cmov .ne .r12 (.reg .rax),
    .alu .add .r9 (.reg .r9), .alu .add .r10 (.reg .r10)]

/-- A batch's start: the count of steps `59` in the low byte of `r8`, above it the
count of batches from `rbp`; `d`, the low words of `f` and `g`, the identity,
and `d ≥ 0`. -/
def dstart : List Instr :=
  [.mov .r8 (.reg .rbp), .alu .add .r8 (.imm 59), .mov .rbx (.mem (sc dsD)), .mov .rcx (.mem (sc dsF)),
    .mov .rbp (.mem (sc dsG)), .mov32 .r9 (.imm 1), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0),
    .mov32 .r12 (.imm 1), .mov .r13 (.reg .rbx), .shift .shr .r13 63, .alu .xor .r13 (.imm 1)]

/-- 59 divsteps, counted down in the low byte of `r8`; then `d` and the matrix
stored, and the count of batches back in `rbp`. -/
def dsteps : Prog isa :=
  .seq (.block dstart) <|
    .seq (.loop (.block (dstep ++ [.alu .sub .r8 (.imm 1), .alu .test .r8 (.imm 255)])) .ne)
    (.block [.store (sc dsD) .rbx, .store (sc dsU) .r9, .store (sc dsV) .r10, .store (sc dsQ) .r11,
      .store (sc dsR) .r12, .mov .rbp (.reg .r8)])

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
    .seq (.block lastSwap) <| .seq (invertDS F) (.block (finish F))

/-- X25519 with the field multiplications `F`. -/
def x25519With (F : Field) : Prog isa := x25519Of F (ladder F)

def x25519 : Prog isa := x25519With baseline

end VG.Impl.X25519.X86_64
