module

public import VerifiedGarbage.Impl.Bignum.X86.PublicRt

/-!
# `2^(10 B) mod M` by word steps (i686)

For the modulus `M` (number 0) of `n_len` bytes, `W' = ⌈n_len / 4⌉` words
up to its top word, which is not zero, and the width `B = 8 ⌈n_len / 8⌉`:
number 4 set to `2^(32 (W' - 1))`, below `M`, then `⌊10 B / 32⌋ - (W' - 1)`
steps `x := x 2^32 mod M`, each a step of long division (Knuth, TAOCP vol. 2,
§4.3.1, Algorithm D), which leave `2^(32 ⌊10 B / 32⌋) mod M`:

* the quotient `q = ⌊x 2^32 / M⌋` is that of `2^z x 2^32` by `2^z M`, for
  the leading zeros `z` of `M`'s top word, whose top word `d` has its top bit
  set: `q̂ = min(⌊(u₂ 2^32 + u₁) / d⌋, 2^32 - 1)` from the top words `u₂`, `u₁`
  of `2^z x` gives `q ≤ q̂ ≤ q + 2`; `2^z` (`p`) and `d` once (`norm`), by
  doublings under a mask, and `u₂`, `u₁` each step by products with `p`
  (`top`), so that `M` and `x` are never shifted;
* `⌊(u₂ 2^32 + u₁) / d⌋` by the reciprocal `v = ⌊(2^64 - 1) / d⌋ - 2^32`
  (Möller and Granlund, "Improved division by invariant integers", IEEE Trans.
  Computers 60(2), 2011, Algorithm 4), with its two corrections by masks
  (`quot`); `v` once, by restoring division, a bit at a time (`recip`);
* `t = x 2^32 - q̂ M` over `W' + 1` words in two's complement (`mulSub`),
  whose carry `hi(q̂ Mᵢ + c) + borrow` fits a word and is kept in the next
  word of `t`;
* `M` added to `t` while it is negative, twice, by a mask (`addBack`);
* `t` back into `x` (`copyBack`).

Every branch and address depends only on `n_len`: the counts are fixed
(31 doublings, 32 bits) or the lengths', and the arithmetic on `M`'s words is
branch-free. Widths are computed from the arguments and kept in registers,
never read back from the working area, so that the taint analysis sees every
address as public; only the steps' count is, which the proof of constant
time relates by its value. The working area's header holds `p`
(160), `d` (164), `v` (168), the mask of `u₂ = d` (172), the steps left
(176) and `q̂` (180), and `t` is number 5.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.R2Words
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicRt

def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

def oP : Nat := 160
def oD : Nat := 164
def oV : Nat := 168
def oMask : Nat := 172
def oSteps : Nat := 176
def oQ : Nat := 180

/-- A header word. -/
def hd (o : Nat) : MemOp := at_ .edi o

/-- `r = 4 W' = 4 ⌈n_len / 4⌉`. -/
def width4 (r : Reg) : List Instr :=
  [.mov r (.mem (argAt 0 1)), .alu .add r (.imm 3), .shift .shr r 2, .alu .add r (.reg r), .alu .add r (.reg r)]

/-- `r = edi + 256 + j B + 4 W' - 4 i`, a pointer to word `W' - i` of number
`j`, and `t = 4 W'`. -/
def topPtr (r : Reg) (j i : Nat) (t : Reg) : List Instr :=
  slotPtr r j t ++ width4 t ++ [.alu .add r (.reg t), .alu .sub r (.imm (BitVec.ofNat 32 (4 * i)))]

/-! ## `p = 2^z` and `d` -/

/-- A doubling of `eax` and `esi` where the top bit of `eax` is clear; `edx`
counts down. -/
def normBit : List Instr :=
  [.mov .ecx (.reg .eax), .shift .shr .ecx 31, .alu .sub .ecx (.imm 1), .mov .ebp (.reg .eax),
    .alu .and .ebp (.reg .ecx), .alu .add .eax (.reg .ebp), .mov .ebp (.reg .esi), .alu .and .ebp (.reg .ecx),
    .alu .add .esi (.reg .ebp), .alu .sub .edx (.imm 1)]

/-- `p = 2^z` at 160 for the leading zeros `z` of `M`'s top word
`M[W' - 1]`, by 31 doublings under a mask; and `d = M[W' - 1] p +
hi(M[W' - 2] p)` at 164. -/
def norm : Prog isa := seqs [
  .block (topPtr .ebx 0 2 .ecx ++
    [.mov .eax (.mem (at_ .ebx 4)), .mov .esi (.imm 1), .mov .edx (.imm 31)]),
  .loop (.block normBit) .ne,
  .block [.store (hd oP) .esi, .mov .ecx (.reg .eax), .mov .eax (.mem (at_ .ebx 0)), .mul .esi,
    .alu .add .ecx (.reg .edx), .store (hd oD) .ecx]]

/-! ## `v` -/

/-- A bit of restoring division by `d` (`esi`) of the remainder `r < d`
(`edx`) and a one bit: `r := 2 r + 1`, its carry into `ebp` (a mask);
subtract `d` if the carry is set or `r ≥ d` (a mask in `ebx`); the quotient
`ecx := 2 ecx + 1` if so, `2 ecx` otherwise; and the count `edi` down. -/
def divBit : List Instr :=
  [.alu .add .edx (.reg .edx), .alu .sbb .ebp (.reg .ebp), .alu .add .edx (.imm 1),
    .mov .eax (.reg .edx), .alu .sub .eax (.reg .esi), .alu .sbb .ebx (.reg .ebx), .alu .xor .ebx (.imm (-1)),
    .alu .or .ebx (.reg .ebp), .mov .eax (.reg .esi), .alu .and .eax (.reg .ebx), .alu .sub .edx (.reg .eax),
    .alu .add .ecx (.reg .ecx), .alu .sub .ecx (.reg .ebx), .alu .sub .edi (.imm 1)]

/-- `v = ⌊((2^32 - 1 - d) 2^32 + 2^32 - 1) / d⌋` at 168, by 32 bits of
restoring division; `edi` counts them, and is set back from argument 4. -/
def recip : Prog isa := seqs [
  .block [.mov .esi (.mem (hd oD)), .mov .edx (.reg .esi), .alu .xor .edx (.imm (-1)), .mov .ecx (.imm 0),
    .mov .edi (.imm 32)],
  .loop (.block divBit) .ne,
  .block [.mov .edi (.mem (argAt 0 4)), .store (hd oV) .ecx]]

/-! ## A step -/

/-- `u₁` into `ebp` and `u₂` into `eax`, the words `W' - 2` and `W' - 1` of
`2^z x` for `x` number 4: `lo(x[W' - 2] p) + hi(x[W' - 3] p)` and
`lo(x[W' - 1] p) + hi(x[W' - 2] p)`. -/
def top : List Instr :=
  topPtr .ebx 4 3 .ecx ++
  [.mov .esi (.mem (hd oP)), .mov .eax (.mem (at_ .ebx 0)), .mul .esi, .mov .ecx (.reg .edx),
    .mov .eax (.mem (at_ .ebx 4)), .mul .esi, .alu .add .eax (.reg .ecx), .mov .ebp (.reg .eax),
    .mov .ecx (.reg .edx), .mov .eax (.mem (at_ .ebx 8)), .mul .esi, .alu .add .eax (.reg .ecx)]

/-- `q̂` at 180 from `u₂` (`eax`) and `u₁` (`ebp`): the mask of `u₂ = d`
(as `u₂ ≤ d`, of `d - u₂ < 1`) at 172 and `u₂` cleared under it; `(q₁, q₀)
= v u₂ + (u₂, u₁)`, the candidate `q₁ + 1` (`ebx`) and its remainder `r =
u₁ - (q₁ + 1) d mod 2^32` (`edx`); one less and `r + d` if `r > q₀`, one
more if then `r ≥ d`; and all ones where `u₂ = d`. -/
def quot : List Instr :=
  [.mov .ecx (.mem (hd oD)), .alu .sub .ecx (.reg .eax), .alu .cmp .ecx (.imm 1), .alu .sbb .ecx (.reg .ecx),
    .store (hd oMask) .ecx, .alu .xor .ecx (.imm (-1)), .alu .and .eax (.reg .ecx),
    .mov .ecx (.reg .eax), .mov .eax (.mem (hd oV)), .mul .ecx, .alu .add .eax (.reg .ebp),
    .alu .adc .edx (.reg .ecx),
    .mov .ebx (.reg .edx), .alu .add .ebx (.imm 1), .mov .ecx (.reg .eax), .mov .eax (.reg .ebx),
    .mov .esi (.mem (hd oD)), .mul .esi, .mov .edx (.reg .ebp), .alu .sub .edx (.reg .eax),
    .alu .cmp .ecx (.reg .edx), .alu .sbb .eax (.reg .eax), .alu .add .ebx (.reg .eax),
    .alu .and .eax (.reg .esi), .alu .add .edx (.reg .eax),
    .mov .eax (.reg .esi), .alu .sub .eax (.imm 1), .alu .cmp .eax (.reg .edx), .alu .adc .ebx (.imm 0),
    .alu .or .ebx (.mem (hd oMask)), .store (hd oQ) .ebx]

/-- `mulSub`'s pointers: `ebx` at `M`, `esi` at `x`, `ebp` at `t`, and
`ecx = q̂`. -/
def subPtrs : List Instr :=
  slotPtr .ebx 0 .edx ++ slotPtr .esi 4 .edx ++ slotPtr .ebp 5 .edx ++ [.mov .ecx (.mem (hd oQ))]

/-- Word 0 of `t = x 2^32 - q̂ M`: `0 - lo(q̂ M₀)`, and the carry
`hi(q̂ M₀) + borrow` into the next word of `t`, which word 1 replaces once it
has read it; then `ebx` at `M₁`, `ebp` at `t₁`, and `edi` counting the
`4 (W' - 1)` bytes of the words before the top. -/
def subHead : List Instr :=
  [.mov .eax (.mem (at_ .ebx 0)), .mul .ecx, .store (at_ .ebp 4) .edx, .mov .edx (.imm 0),
    .alu .sub .edx (.reg .eax), .store (at_ .ebp 0) .edx, .alu .sbb .eax (.reg .eax), .mov .edx (.mem (at_ .ebp 4)),
    .alu .sub .edx (.reg .eax), .store (at_ .ebp 4) .edx] ++ width4 .edi ++
  [.alu .sub .edi (.imm 4), .alu .add .ebx (.imm 4), .alu .add .ebp (.imm 4)]

/-- Word `i` of `t`: `x[i - 1] - lo(q̂ Mᵢ + c)` for the carry `c` in it, and
the carry `hi(q̂ Mᵢ + c) + borrow` into the next. -/
def subBody : List Instr :=
  [.mov .eax (.mem (at_ .ebx 0)), .mul .ecx, .alu .add .eax (.mem (at_ .ebp 0)), .alu .adc .edx (.imm 0),
    .store (at_ .ebp 4) .edx, .mov .edx (.mem (at_ .esi 0)), .alu .sub .edx (.reg .eax), .store (at_ .ebp 0) .edx,
    .alu .sbb .eax (.reg .eax), .mov .edx (.mem (at_ .ebp 4)), .alu .sub .edx (.reg .eax), .store (at_ .ebp 4) .edx,
    .alu .add .ebx (.imm 4), .alu .add .esi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .edi (.imm 4)]

/-- Word `W'` of `t`: `x[W' - 1] - c`; and `edi` set back from argument 4. -/
def subTop : List Instr :=
  [.mov .edx (.mem (at_ .esi 0)), .alu .sub .edx (.mem (at_ .ebp 0)), .store (at_ .ebp 0) .edx,
    .mov .edi (.mem (argAt 0 4))]

/-- `t := x 2^32 - q̂ M` over `W' + 1` words, modulo `2^(32 (W' + 1))`. -/
def mulSub : Prog isa := seqs [.block (subPtrs ++ subHead), .loop (.block subBody) .ne, .block subTop]

/-- The mask of `t`'s sign (the top bit of its word `W'`) into `ecx`, no
carry in `esi`; `ebx` at `M`, `ebp` at `t`, `edi` counting `4 W'` bytes. -/
def addHead : List Instr :=
  slotPtr .ebx 0 .edx ++ slotPtr .ebp 5 .edx ++ width4 .edi ++
  [.mov .eax (.reg .ebp), .alu .add .eax (.reg .edi), .mov .eax (.mem (at_ .eax 0)), .alu .add .eax (.reg .eax),
    .alu .sbb .ecx (.reg .ecx), .mov .esi (.imm 0)]

/-- Word `i` of `t := t + (M & mask)`, the carry in `esi` (a mask). -/
def addBody : List Instr :=
  [.mov .eax (.mem (at_ .ebx 0)), .alu .and .eax (.reg .ecx), .alu .add .esi (.reg .esi),
    .alu .adc .eax (.mem (at_ .ebp 0)), .store (at_ .ebp 0) .eax, .alu .sbb .esi (.reg .esi),
    .alu .add .ebx (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .edi (.imm 4)]

/-- Word `W'` of `t` plus the carry; `edi` set back from argument 4. -/
def addTop : List Instr :=
  [.mov .eax (.mem (at_ .ebp 0)), .alu .sub .eax (.reg .esi), .store (at_ .ebp 0) .eax,
    .mov .edi (.mem (argAt 0 4))]

/-- `t := t + M` if `t` is negative, modulo `2^(32 (W' + 1))`. -/
def addBack : Prog isa := seqs [.block addHead, .loop (.block addBody) .ne, .block addTop]

/-- The `W'` words of `t` into `x`; `edi` set back from argument 4. -/
def copyBack : Prog isa := seqs [
  .block (slotPtr .esi 5 .edx ++ slotPtr .ebp 4 .edx ++ width4 .edi),
  .loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
    .alu .add .ebp (.imm 4), .alu .sub .edi (.imm 4)]) .ne,
  .block [.mov .edi (.mem (argAt 0 4))]]

/-- `x := x 2^32 mod M`. -/
def step : Prog isa := seqs [.block (top ++ quot), mulSub, addBack, addBack, copyBack]

/-- The steps' count `⌊5 B / 16⌋ - W' + 1` at 176. -/
def count : List Instr :=
  widthB 0 .eax ++ [.mov .ecx (.reg .eax), .alu .add .eax (.reg .ecx), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .ecx), .shift .shr .eax 4, .alu .add .eax (.imm 1)] ++ width4 .edx ++
  [.shift .shr .edx 2, .alu .sub .eax (.reg .edx), .store (hd oSteps) .eax]

/-- The steps, their count at 176. -/
def steps : Prog isa :=
  .seq (.block count)
    (.loop (.seq step (.block [.mov .eax (.mem (hd oSteps)), .alu .sub .eax (.imm 1), .store (hd oSteps) .eax])) .ne)

/-! ## `2^(10 B) mod M` -/

/-- Number 4 set to `2^(32 (W' - 1))`. -/
def seedX : Prog isa :=
  .seq (zero 4) (.block (topPtr .eax 4 1 .ecx ++ [.mov .edx (.imm 1), .store (at_ .eax 0) .edx]))

/-- `10 B mod 32 = 16 (B / 8 mod 2)` doublings of number 4 modulo `M`,
counted by `esi`. -/
def tail : Prog isa :=
  .seq (.block (widthB 0 .esi ++ [.shift .shr .esi 3, .alu .and .esi (.imm 1), .alu .add .esi (.reg .esi),
      .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi)]))
    (.ite .e (.block []) (.loop (doubleStep 4) .ne))

/-- Number 4 set to `2^(10 B) mod M`. -/
def run : Prog isa := seqs [norm, recip, seedX, steps, tail]

end VG.Impl.Bignum.X86.R2Words
