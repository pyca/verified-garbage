module

public import VerifiedGarbage.Impl.Bignum.Arm.Round

/-!
# Two Montgomery rows a pass, with UMAAL

A replacement for `Fios.round` that does the rows of two words `a₀ = aᵢ`
and `a₁ = aᵢ₊₁` of the first operand in one scan of the accumulator `T`:
row `i` takes word `j + 1` of `b` and `m` while row `i + 1` takes word `j`,
on the output of row `i` at word `j`, which stays in `r6` between them. Each
word of the accumulator is loaded and stored once for both rows, and the
four products of a word go to four independent carry chains:

* `r1 = a₀`, `r2 = q₀` (the quotient of row `i`), carries `r7` (product) and
  `r8` (cancellation);
* `r9 = a₁`, `r10 = q₁`, carries `r5` and `r11`;
* `r0` the accumulator, `r12` `b`, `r4` `m`, `lr` the count, `r6` the word
  in flight and `r3` the word of `b` or `m` multiplied into it.

The quotients are found as `Fios.first` finds its own: `q₀` from the low
word of row `i`'s first product, `q₁` from row `i`'s first output word plus
`a₁ b₀`. After the pass the accumulator holds `(T + (a₀ + 2³² a₁) b +
(q₀ + 2³² q₁) m) / 2⁶⁴` in `n + 1` words, and `finish` clears its top word,
advances the first operand's pointer by two words and the remaining rounds
by two. `n` is even and at least 4, so the loop's `n - 2` words are pairs.

Every address is a pointer plus a constant and every branch compares the
public count: the timing does not depend on the numbers.
-/

@[expose] public section
namespace VG.Impl.Bignum.Arm.Fios2
open VG VG.Arm

/-- Enter with the temporary in `r0`: the two words of `a`, the count, the
pointers to `b`, `m` and the accumulator, the inverse (twice: each quotient
register is the inverse until it is multiplied), and clear carries. -/
def args : List Instr :=
  [.ldr .r3 .r0 16, .ldr .r1 .r3 0, .ldr .r9 .r3 4, .ldr .lr .r0 0,
   .ldr .r12 .r0 4, .ldr .r4 .r0 8, .ldr .r2 .r0 12, .mov .r10 (.reg .r2),
   .ldr .r0 .r0 28, .mov .r7 (.imm 0), .mov .r8 (.imm 0), .mov .r5 (.imm 0),
   .mov .r11 (.imm 0)]

/-- `r6 += [p + k] · s + c`, the high word to the carry `c`, through `r3`. -/
def macAt (p : Reg) (k : Nat) (c s : Reg) : Prog isa :=
  .seq (.block [.ldr .r3 p k]) (.block [.umaal .r6 c .r3 s])

/-- Row `i` at word `j + 1` and row `i + 1` at word `j`, with `r0`, `r12`
and `r4` at word `j - 1` less `k`: the accumulator's word `j + 1` in, row
`i + 1`'s word `j - 1` out. -/
def step (k : Nat) : Prog isa :=
  .seq (.block [.ldr .r6 .r0 (k + 8)]) <|
  .seq (macAt .r12 (k + 8) .r7 .r1) <|
  .seq (macAt .r4 (k + 8) .r8 .r2) <|
  .seq (macAt .r12 (k + 4) .r5 .r9) <|
  .seq (macAt .r4 (k + 4) .r11 .r10) <|
    .block [.str .r6 .r0 k]

def advance : List Instr :=
  [.dp .add .r0 .r0 (.imm 8), .dp .add .r12 .r12 (.imm 8),
   .dp .add .r4 .r4 (.imm 8), .subs .lr .lr (.imm 2)]

def body : Prog isa := .seq (step 0) (.seq (step 4) (.block advance))

def loop : Prog isa := .loop body .ne

/-- Row `i` at words 0 and 1 and row `i + 1` at word 0, each quotient from
the low word it cancels; the cancelled words are discarded. -/
def first : Prog isa :=
  .seq (.block [.ldr .r6 .r0 0]) <|
  .seq (macAt .r12 0 .r7 .r1) <|
  .seq (.block [.mul .r2 .r2 .r6]) <|
  .seq (macAt .r4 0 .r8 .r2) <|
  .seq (.block [.ldr .r6 .r0 4]) <|
  .seq (macAt .r12 4 .r7 .r1) <|
  .seq (macAt .r4 4 .r8 .r2) <|
  .seq (macAt .r12 0 .r5 .r9) <|
  .seq (.block [.mul .r10 .r10 .r6]) <|
  .seq (macAt .r4 0 .r11 .r10) <|
    .block [.dp .sub .lr .lr (.imm 2)]

/-- Row `i`'s top: the accumulator's words `n` and `n + 1` plus its carries,
into `r3:r6`. -/
def rowTop : List Instr :=
  [.ldr .r6 .r0 8, .ldr .r3 .r0 12, .adds .r6 .r6 (.reg .r7), .adc .r3 .r3 (.imm 0),
   .adds .r6 .r6 (.reg .r8), .adc .r3 .r3 (.imm 0)]

/-- Row `i + 1` at word `n - 1`, through `r7`, row `i`'s carries being spent. -/
def lastAt (p c s : Reg) : Prog isa :=
  .seq (.block [.ldr .r7 p 4]) (.block [.umaal .r6 c .r7 s])

/-- Row `i + 1`'s top: row `i`'s top word plus its carries, into words `n - 1`
and `n`; `r0` then points to word `n + 1`. -/
def pairTop : List Instr :=
  [.adds .r3 .r3 (.reg .r5), .mov .r6 (.imm 0), .adc .r6 .r6 (.imm 0),
   .adds .r3 .r3 (.reg .r11), .adc .r6 .r6 (.imm 0),
   .str .r3 .r0 4, .str .r6 .r0 8, .dp .add .r0 .r0 (.imm 12)]

def top : Prog isa :=
  .seq (.block rowTop) <|
  .seq (lastAt .r12 .r5 .r9) <|
  .seq (lastAt .r4 .r11 .r10) <|
  .seq (.block [.str .r6 .r0 0]) (.block pairTop)

def code : Prog isa := .seq first (.seq loop top)

/-- `roundFinish` for two rows: the first operand's pointer moves two words
and the remaining rounds down by two. -/
def finish : List Instr :=
  clearTop ++ [.ldr .r4 .r0 16, .dp .add .r4 .r4 (.imm 8), .str .r4 .r0 16] ++
    [.ldr .lr .r0 20, .subs .lr .lr (.imm 2), .str .lr .r0 20]

def round : Prog isa := .seq (.block args) (.seq code (.block finish))

end VG.Impl.Bignum.Arm.Fios2
