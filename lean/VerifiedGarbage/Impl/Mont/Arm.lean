import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Impl.Mont.Mod

/-!
# Montgomery arithmetic modulo an odd multiword modulus, on 32-bit ARM

Arithmetic modulo an odd `m < 2^(64 n)`, on numbers below `m` held in the
working space, whose base is in `r12`, as `2n` little-endian 32-bit words
at a constant offset (the same bytes as the `n` 64-bit words of the other
targets, so the slots, the modulus `[M.mo]` and the temporary area `[M.tmp]`
are laid out as theirs).

The only multiplication is `mul` (the low 32 bits of a product) and `adc`
sets no flags, so the arithmetic is on `D = 4n` digits of 16 bits, each in a
word of its own, as for X25519 (`Impl/X25519/Arm.lean`): a digit times a
digit, plus a digit and a carry below `2¹⁶`, fits in 32 bits, and the carry
is the high half. A number's digit `2k` is the low half of its word `k`, and
digit `2k + 1` the high half. `r6` holds `0xffff`. With `R = 2^(16 D) =
2^(64 n)` and `m' = -m⁻¹ mod 2¹⁶` (the low half of `M.minv`):

* `mul acc o a b`: `[o] = [a] [b] R⁻¹ mod m`, by coarsely integrated operand
  scanning (CIOS) on digits, with the accumulator in memory: `2D + 2`
  digits at `[acc]`, cleared, and a window of them at `[r0 + acc]`, `r0`
  starting at `r12`. Each of the `D / 2` iterations of the loop (counted
  down in `r9`; `r1` points to word `i` of `[a]`) does two rows, for the
  low and the high digit of that word: the window `+= u [b]` (`mulRow`),
  then `+= q m` for `q = t₀ m' mod 2¹⁶`, which clears the window's low
  digit, and the window moves up a digit (`r0 += 4`) instead of shifting the
  accumulator. Its last `D + 1` digits are then below `2m` and reduced by
  `csub`.
* `add acc o a b`: the digits of `[a] + [b]` at `[acc]`, then `csub`;
  `sub acc o a b`: the digits of `[a] + m - [b]` (each digit
  `a_j + m_j + (2¹⁶ - 1 - b_j)` plus the carry, from a carry of 1, which
  adds `2^(16 D)`, taken off the top digit), then `csub`.
* `csub src o`: the number below `2m` at `[src]` (`D` digits and a top digit,
  0 or 1) reduced modulo `m` into `[o]`: the digits of its difference with
  `m` (each `t_j + (2¹⁶ - 1 - m_j)` plus the carry, from 1) are packed into
  `[M.tmp]`; the carry out plus the top digit is 1 if it did not borrow, and
  its negation selects the difference or the number, packed into `[o]`.

Every multiplication is `mul`, every selection a mask, and every address
`r12`, `r0` or `r1` (`r12` plus a multiple of 4 counted by the loop) plus a
constant: nothing but `r12` may affect timing. The operations use `r0`–`r9`,
and write only `[o]`, `[acc]` and `[M.tmp]`.
-/

namespace VG.Impl.Mont.Arm

open VG.Arm

/-- The working space's base. -/
abbrev wb : Reg := .r12

/-- The number of 32-bit words of a number. -/
def words (M : Mod) : Nat := 2 * M.n

/-- The number of 16-bit digits of a number. -/
def digits (M : Mod) : Nat := 4 * M.n

/-- `-m⁻¹ mod 2¹⁶`. -/
def minv16 (M : Mod) : BitVec 16 := M.minv.setWidth 16

/-- `d = ` digit `h` (0: low, 1: high) of the word in `w`. -/
def half (d w : Reg) (h : Nat) : Instr :=
  if h = 0 then .dp .and d w (.reg .r6) else .mov d (.shifted w .lsr 16)

/-- `r7 = ` digit `j` of the number at `[rb + src]`. -/
def digitAt (rb : Reg) (src j : Nat) : List Instr := [.ldr .r7 rb (src + 4 * (j / 2)), half .r7 .r7 (j % 2)]

/-- `[r0 + acc + 4j] += r2 · d_j + r3`, its digit kept and its carry to `r3`,
for digit `j` of the number at `[rb + src]` (a multiply-accumulate step,
which never overflows). -/
def mulStep (acc : Nat) (rb : Reg) (src j : Nat) : List Instr :=
  digitAt rb src j ++
  ([.mul .r7 .r2 .r7, .ldr .r5 .r0 (acc + 4 * j), .dp .add .r5 .r5 (.reg .r7), .dp .add .r5 .r5 (.reg .r3),
    .dp .and .r7 .r5 (.reg .r6), .str .r7 .r0 (acc + 4 * j), .mov .r3 (.shifted .r5 .lsr 16)] : List Instr)

/-- The carry `r3` added into the window's digits `D` and `D + 1`. -/
def carryUp (acc D : Nat) : List Instr :=
  [.ldr .r5 .r0 (acc + 4 * D), .dp .add .r5 .r5 (.reg .r3), .dp .and .r7 .r5 (.reg .r6),
    .str .r7 .r0 (acc + 4 * D), .ldr .r7 .r0 (acc + 4 * D + 4), .dp .add .r7 .r7 (.shifted .r5 .lsr 16),
    .str .r7 .r0 (acc + 4 * D + 4)]

/-- The window `+= r2 · [rb + src]`, `D` digits, with its carry. -/
def mulRow (acc : Nat) (rb : Reg) (src D : Nat) : List Instr :=
  .mov .r3 (.imm 0) :: (List.range D).flatMap (mulStep acc rb src) ++ carryUp acc D

/-- A row for the digit `h` of `r8` (a word of `[a]`): the window
`+= u [b]`, then `+= q m` with `q = t₀ m' mod 2¹⁶`, after which its low
digit is zero; then the window moves up a digit. `[b]` is at `[rb + b]`. -/
def digitRow (M : Mod) (acc : Nat) (rb : Reg) (b h : Nat) : List Instr :=
  let D := digits M
  [half .r2 .r8 h] ++ mulRow acc rb b D ++
  ([.ldr .r2 .r0 acc, .movw .r7 (minv16 M), .mul .r2 .r2 .r7, .dp .and .r2 .r2 (.reg .r6)] : List Instr) ++
    mulRow acc wb M.mo D ++
  ([.dp .add .r0 .r0 (.imm 4)] : List Instr)

/-- An iteration of `mul`: the rows of both digits of word `r1` of `[a]`,
then the next word, and the count. -/
def row (M : Mod) (acc a : Nat) (rb : Reg) (b : Nat) : List Instr :=
  ([.ldr .r8 .r1 a] : List Instr) ++ digitRow M acc rb b 0 ++ digitRow M acc rb b 1 ++
  ([.dp .add .r1 .r1 (.imm 4), .subs .r9 .r9 (.imm 1)] : List Instr)

/-- `[acc]`, `k` words, cleared (through `r7`). -/
def zeros (acc k : Nat) : List Instr :=
  .mov .r7 (.imm 0) :: (List.range k).map fun j => .str .r7 wb (acc + 4 * j)

/-- `r6 = 0xffff`. -/
def mask16 : Instr := .movw .r6 0xffff

/-- Digit `j` of `[src] - m` (from the carry `r3`, 1 for the first), into
`r5`, its carry to `r3`; `r7` holds word `j / 2` of `m`. -/
def diffDigit (src j : Nat) : List Instr :=
  [.ldr .r5 wb (src + 4 * j), half .r4 .r7 (j % 2), .dp .add .r5 .r5 (.reg .r6), .dp .sub .r5 .r5 (.reg .r4),
    .dp .add .r5 .r5 (.reg .r3), .mov .r3 (.shifted .r5 .lsr 16)]

/-- Word `k` of `[src] - m`, packed into `[tmp]`, through `r8`. -/
def diffWord (M : Mod) (src k : Nat) : List Instr :=
  ([.ldr .r7 wb (M.mo + 4 * k)] : List Instr) ++ diffDigit src (2 * k) ++ ([.dp .and .r8 .r5 (.reg .r6)] : List Instr) ++
    diffDigit src (2 * k + 1) ++ ([.dp .orr .r8 .r8 (.shifted .r5 .lsl 16), .str .r8 wb (M.tmp + 4 * k)] : List Instr)

/-- Word `k` of the digits at `[src]`, packed, or of `[tmp]` where the mask
`r3` is all ones, into `[ro + o]`. -/
def selWord (M : Mod) (src : Nat) (ro : Reg) (o k : Nat) : List Instr :=
  [.ldr .r5 wb (src + 8 * k), .ldr .r7 wb (src + 8 * k + 4), .dp .orr .r5 .r5 (.shifted .r7 .lsl 16),
    .ldr .r7 wb (M.tmp + 4 * k), .dp .eor .r7 .r7 (.reg .r5), .dp .and .r7 .r7 (.reg .r3),
    .dp .eor .r5 .r5 (.reg .r7), .str .r5 ro (o + 4 * k)]

/-- The number at `[src]` (`D` digits, then a top digit 0 or 1), below `2m`,
reduced modulo `m` into `[ro + o]`: the difference with `m` is packed into
`[tmp]`; `r3` is 1 if it did not borrow, and its negation selects it. -/
def csub (M : Mod) (src : Nat) (ro : Reg) (o : Nat) : List Instr :=
  [mask16, .mov .r3 (.imm 1)] ++ (List.range (words M)).flatMap (diffWord M src) ++
  ([.ldr .r5 wb (src + 4 * digits M), .dp .add .r3 .r3 (.reg .r5), .mov .r4 (.imm 0),
    .dp .sub .r3 .r4 (.reg .r3)] : List Instr) ++
  (List.range (words M)).flatMap (selWord M src ro o)

/-- `[ro + o] = [ra + a] [rb + b] R⁻¹ mod m` (`o` may be `a` or `b`). -/
def mulR (M : Mod) (acc o a b : Nat) (ra rb ro : Reg) : Prog isa :=
  .seq (.block (zeros acc (2 * digits M + 2) ++
    [mask16, .mov .r0 (.reg wb), .mov .r1 (.reg ra), .mov .r9 (.imm (BitVec.ofNat 32 (words M)))])) <|
  .seq (.loop (.block (row M acc a rb b)) .ne) <|
    .block (csub M (acc + 4 * digits M) ro o)

/-- `[o] = [a] [b] R⁻¹ mod m` (`o` may be `a` or `b`). -/
def mul (M : Mod) (acc o a b : Nat) : Prog isa := mulR M acc o a b wb wb wb

/-- Digit `j` of `[a] + [b]` (`r7`, `r8` hold their words `j / 2`), from the
carry `r3`, to `[acc]`, its carry to `r3`. -/
def addDigit (acc j : Nat) : List Instr :=
  [half .r4 .r7 (j % 2), half .r5 .r8 (j % 2), .dp .add .r4 .r4 (.reg .r5), .dp .add .r4 .r4 (.reg .r3),
    .dp .and .r5 .r4 (.reg .r6), .str .r5 wb (acc + 4 * j), .mov .r3 (.shifted .r4 .lsr 16)]

/-- `[ro + o] = [ra + a] + [rb + b] mod m`. -/
def addR (M : Mod) (acc o a b : Nat) (ra rb ro : Reg) : List Instr :=
  [mask16, .mov .r3 (.imm 0)] ++
  (List.range (words M)).flatMap (fun k =>
    ([.ldr .r7 ra (a + 4 * k), .ldr .r8 rb (b + 4 * k)] : List Instr) ++ addDigit acc (2 * k) ++ addDigit acc (2 * k + 1)) ++
  ([.str .r3 wb (acc + 4 * digits M)] : List Instr) ++ csub M acc ro o

/-- `[o] = [a] + [b] mod m`. -/
def add (M : Mod) (acc o a b : Nat) : List Instr := addR M acc o a b wb wb wb

/-- Digit `j` of `[a] + m - [b]` (`r7`, `r8`, `r9` hold the words `j / 2` of
`[a]`, `[b]` and `m`), from the carry `r3`, to `[acc]`, its carry to `r3`. -/
def subDigit (acc j : Nat) : List Instr :=
  [half .r4 .r7 (j % 2), half .r5 .r9 (j % 2), .dp .add .r4 .r4 (.reg .r5), .dp .add .r4 .r4 (.reg .r6),
    half .r5 .r8 (j % 2), .dp .sub .r4 .r4 (.reg .r5), .dp .add .r4 .r4 (.reg .r3),
    .dp .and .r5 .r4 (.reg .r6), .str .r5 wb (acc + 4 * j), .mov .r3 (.shifted .r4 .lsr 16)]

/-- `[ro + o] = [ra + a] - [rb + b] mod m`, as `[a] + m - [b]` reduced. -/
def subR (M : Mod) (acc o a b : Nat) (ra rb ro : Reg) : List Instr :=
  [mask16, .mov .r3 (.imm 1)] ++
  (List.range (words M)).flatMap (fun k =>
    ([.ldr .r7 ra (a + 4 * k), .ldr .r8 rb (b + 4 * k), .ldr .r9 wb (M.mo + 4 * k)] : List Instr) ++
      subDigit acc (2 * k) ++ subDigit acc (2 * k + 1)) ++
  ([.dp .sub .r3 .r3 (.imm 1), .str .r3 wb (acc + 4 * digits M)] : List Instr) ++ csub M acc ro o

/-- `[o] = [a] - [b] mod m`, as `[a] + m - [b]` reduced. -/
def sub (M : Mod) (acc o a b : Nat) : List Instr := subR M acc o a b wb wb wb

/-- `r4 = x mod 2³²`. -/
def movImm (x : Nat) : List Instr :=
  [.movw .r4 (BitVec.ofNat 16 x), .movt .r4 (BitVec.ofNat 16 (x >>> 16))]

/-- `[r12 + o] = x`, `n` words, through `r4`. -/
def setConst (n : Nat) (o x : Nat) : List Instr :=
  (List.range (2 * n)).flatMap fun j => movImm (x >>> (32 * j)) ++ ([.str .r4 wb (o + 4 * j)] : List Instr)

end VG.Impl.Mont.Arm
