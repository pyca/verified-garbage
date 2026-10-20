module

public import VerifiedGarbage.Impl.Mont.Arm

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM

DSA's numbers are up to 96 words and its moduli are supplied at run time,
so its arithmetic loops over words where the fixed-modulus code
(`Impl/Mont/Arm.lean`) unrolls them, and loads `-m⁻¹ mod 2¹⁶` from the
working space. As there, the only multiplication is `mul` and `adc` sets
no flags, so numbers are processed as 16-bit digits: a digit times a digit,
plus a digit and a carry below `2¹⁶`, fits in a word.

The working space's base is in `r12`. Its arrays lie at offsets up to
`2¹⁶`, past the 4096 bytes an immediate offset reaches, so every loop
reaches its arrays through pointers it sets from `r12` (`ptr`) and moves up
by a word (or two, for an array of digits), and ends when its first pointer
reaches the end in `r9`. A number of `n` 64-bit words is `W = 2n` 32-bit
words, `D = 4n` digits; an array of digits holds one a word.

* `zeros k o`, `setConst k o x`: `k` words.
* `addD M acc o a b`: `[o] = [a] + [b] mod m`, through the digits of
  `[a] + [b]` at `[acc]` and `csubD`.
* `csubD M src o`: the `D` digits and top digit at `[src]`, a number below
  `2m`, reduced modulo `m` into `[o]` (through `[M.tmp]`): its difference
  with `m`, packed, if that did not borrow, else itself.
* `mul M inv acc o a b`: `[o] = [a] [b] R⁻¹ mod m` (`R = 2^(16 D)`) by CIOS
  on digits, as the fixed-modulus `mul`, with `m'` at `[inv]`.
* `selectW k src tmp o`: `[o] = [tmp]` where the mask `r3` is all ones, else
  `[src]`.

The operations write `r0`–`r10` and the flags, and leave `r11`, `r12` and
`lr` alone, for their callers' loops. Every address is `r12` plus a public
offset, or a pointer that moves by a public step, and every branch compares
two pointers: no operand affects timing.
-/

@[expose] public section

namespace VG.Impl.Mont.Arm.Dynamic

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm

/-- `d = r12 + k`, for `k < 2¹⁶`. -/
def ptr (d : Reg) (k : Nat) : List Instr := [.movw d (BitVec.ofNat 16 k), .dp .add d .r12 (.reg d)]

/-- `body` until `p` reaches `r9`; `body` moves `p` up. -/
def ptrLoop (p : Reg) (body : List Instr) : Prog isa := .loop (.block (body ++ [.cmp p (.reg .r9)])) .ne

/-- `p += k` (an encodable step). -/
def bump (p : Reg) (k : Nat) : Instr := .dp .add p p (.imm (BitVec.ofNat 32 k))

/-! ## Words -/

/-- `[o] = 0`, `k > 0` words. -/
def zeros (k o : Nat) : Prog isa :=
  .seq (.block (ptr .r10 o ++ ptr .r9 (o + 4 * k) ++ [.mov .r7 (.imm 0)]))
    (ptrLoop .r10 [.str .r7 .r10 0, bump .r10 4])

/-- `[o] = x`, `k > 0` words: zeros, then `x`'s nonzero words. -/
def setConst (k o x : Nat) : Prog isa :=
  .seq (zeros k o) (.block (ptr .r10 o ++ (List.range k).flatMap fun j =>
    if x >>> (32 * j) % 2 ^ 32 = 0 then [] else movImm (x >>> (32 * j)) ++ [.str .r4 .r10 (4 * j)]))

/-- `[o] = [tmp]` where the mask `r3` is all ones, else `[src]`, `k > 0` words. -/
def selectW (k src tmp o : Nat) : Prog isa :=
  .seq (.block (ptr .r10 src ++ ptr .r8 tmp ++ ptr .r1 o ++ ptr .r9 (src + 4 * k)))
    (ptrLoop .r10 [.ldr .r5 .r10 0, .ldr .r7 .r8 0, .dp .eor .r7 .r7 (.reg .r5), .dp .and .r7 .r7 (.reg .r3),
      .dp .eor .r5 .r5 (.reg .r7), .str .r5 .r1 0, bump .r10 4, bump .r8 4, bump .r1 4])

/-! ## Digits -/

/-- Digit `h` of `[a] + [b]` (words in `r7` and `r2`), from the carry `r3`,
to `[r8 + 4h]`, its carry to `r3`. -/
def addDigitD (h : Nat) : List Instr :=
  [half .r4 .r7 h, half .r5 .r2 h, .dp .add .r4 .r4 (.reg .r5), .dp .add .r4 .r4 (.reg .r3),
    .dp .and .r5 .r4 (.reg .r6), .str .r5 .r8 (4 * h), .mov .r3 (.shifted .r4 .lsr 16)]

/-- The digits of `[a] + [b]` at `[acc]`, `D` digits and the carry. -/
def addDigits (M : Mod) (acc a b : Nat) : Prog isa :=
  .seq (.block ([mask16, .mov .r3 (.imm 0)] ++ ptr .r10 a ++ ptr .r0 b ++ ptr .r8 acc ++
      ptr .r9 (a + 4 * words M)))
  (.seq (ptrLoop .r10 ([.ldr .r7 .r10 0, .ldr .r2 .r0 0] ++ addDigitD 0 ++ addDigitD 1 ++
      [bump .r10 4, bump .r0 4, bump .r8 8]))
    (.block [.str .r3 .r8 0]))

/-- Digit `h` of `[src] - m` (the digit at `[r10 + 4h]`, `m`'s word in
`r7`), from the carry `r3`, into `r5`, its carry to `r3`. -/
def diffDigitD (h : Nat) : List Instr :=
  [.ldr .r5 .r10 (4 * h), half .r4 .r7 h, .dp .add .r5 .r5 (.reg .r6), .dp .sub .r5 .r5 (.reg .r4),
    .dp .add .r5 .r5 (.reg .r3), .mov .r3 (.shifted .r5 .lsr 16)]

/-- The number at `[src]` (`D` digits, then a top digit 0 or 1), below `2m`,
reduced modulo `m` into `[o]`: the difference with `m` is packed into
`[tmp]`; `r3` is 1 if it did not borrow, and its negation selects it. -/
def csubD (M : Mod) (src o : Nat) : Prog isa :=
  .seq (.block ([mask16, .mov .r3 (.imm 1)] ++ ptr .r10 src ++ ptr .r1 M.mo ++ ptr .r8 M.tmp ++
      ptr .r9 (M.mo + 4 * words M)))
  (.seq (ptrLoop .r1 ([.ldr .r7 .r1 0] ++ diffDigitD 0 ++ [.dp .and .r2 .r5 (.reg .r6)] ++ diffDigitD 1 ++
      [.dp .orr .r2 .r2 (.shifted .r5 .lsl 16), .str .r2 .r8 0, bump .r10 8, bump .r1 4, bump .r8 4]))
  (.seq (.block [.ldr .r5 .r10 0, .dp .add .r3 .r3 (.reg .r5), .mov .r4 (.imm 0), .dp .sub .r3 .r4 (.reg .r3)])
  (.seq (.block (ptr .r10 src ++ ptr .r8 M.tmp ++ ptr .r1 o ++ ptr .r9 (M.tmp + 4 * words M)))
    (ptrLoop .r8 [.ldr .r5 .r10 0, .ldr .r7 .r10 4, .dp .orr .r5 .r5 (.shifted .r7 .lsl 16),
      .ldr .r7 .r8 0, .dp .eor .r7 .r7 (.reg .r5), .dp .and .r7 .r7 (.reg .r3),
      .dp .eor .r5 .r5 (.reg .r7), .str .r5 .r1 0, bump .r10 8, bump .r8 4, bump .r1 4]))))

/-- `[o] = [a] + [b] mod m`. -/
def addD (M : Mod) (acc o a b : Nat) : Prog isa := .seq (addDigits M acc a b) (csubD M acc o)

/-! ## The multiplication -/

/-- Digit `h` of the word in `r7`, times `r2`, plus the carry `r3`, added to
the window's digit at `[r10 + 4h]` (by `mla`), its carry to `r3`. -/
def macD (h : Nat) : List Instr :=
  [half .r4 .r7 h, .ldr .r5 .r10 (4 * h), .mla .r5 .r2 .r4 .r5,
    .dp .add .r5 .r5 (.reg .r3), .dp .and .r4 .r5 (.reg .r6), .str .r4 .r10 (4 * h),
    .mov .r3 (.shifted .r5 .lsr 16)]

/-- The window at `r0` `+= r2 · [src]` (`D` digits), with its carry into its
digits `D` and `D + 1`. -/
def mulRowD (M : Mod) (src : Nat) : Prog isa :=
  .seq (.block ([.mov .r3 (.imm 0), .mov .r10 (.reg .r0)] ++ ptr .r8 src ++ ptr .r9 (src + 4 * words M)))
  (.seq (ptrLoop .r8 ([.ldr .r7 .r8 0] ++ macD 0 ++ macD 1 ++ [bump .r10 8, bump .r8 4]))
    (.block [.ldr .r5 .r10 0, .dp .add .r5 .r5 (.reg .r3), .dp .and .r7 .r5 (.reg .r6), .str .r7 .r10 0,
      .ldr .r7 .r10 4, .dp .add .r7 .r7 (.shifted .r5 .lsr 16), .str .r7 .r10 4]))

/-- A row for digit `h` of the word at `[r1]` of `[a]`: the window `+= u [b]`,
then `+= q m` for `q = t₀ m' mod 2¹⁶` (`m'` at `[inv]`), which clears its low
digit; then the window moves up a digit. -/
def digitRowD (M : Mod) (inv b h : Nat) : Prog isa :=
  .seq (.block [.ldr .r2 .r1 0, half .r2 .r2 h]) <|
  .seq (mulRowD M b) <|
  .seq (.block [.ldr .r2 .r0 0, .ldr .r4 .r12 inv, .mul .r2 .r2 .r4, .dp .and .r2 .r2 (.reg .r6)]) <|
  .seq (mulRowD M M.mo) (.block [bump .r0 4])

/-- An iteration: the rows of both digits of a word of `[a]`, then the next. -/
def rowD (M : Mod) (inv a b : Nat) : Prog isa :=
  .seq (digitRowD M inv b 0) <| .seq (digitRowD M inv b 1)
    (.block ([bump .r1 4] ++ ptr .r9 (a + 4 * words M) ++ [.cmp .r1 (.reg .r9)]))

/-- `[o] = [a] [b] R⁻¹ mod m`, `m'` at `[inv]`, through `2D + 2` digits at
`[acc]` (`o` may be `a` or `b`). -/
def mul (M : Mod) (inv acc o a b : Nat) : Prog isa :=
  .seq (zeros (2 * digits M + 2) acc) <|
  .seq (.block ([mask16] ++ ptr .r0 acc ++ ptr .r1 a)) <|
  .seq (.loop (rowD M inv a b) .ne)
    (csubD M (acc + 4 * digits M) o)

end VG.Impl.Mont.Arm.Dynamic
