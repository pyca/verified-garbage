module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Mont.Mod

/-!
# Montgomery arithmetic modulo an odd multiword modulus, on PPC64LE

Arithmetic modulo an odd `m < 2^(64 n)`, on numbers below `m` held in the
working space, whose base is in `r3`, as `n` little-endian 64-bit words at
a constant offset, or at a register (`[a]` at `r5`, `[b]` at `r6`, `[o]` at
`r4`).

The model has no carry, so the arithmetic is on `D = 2n` digits of 32 bits,
the 32-bit words of the numbers (`lwz` loads one, zero-extended; `stw`
stores the low 32 bits of a register), as on 32-bit ARM on digits of 16 bits
(`Impl/Mont/Arm.lean`): a digit times a digit, plus a digit and a carry
below `2³²`, fits in 64 bits (`(2³² - 1)² + 2 (2³² - 1) = 2⁶⁴ - 1`), and the
carry is the high half. With `R = 2^(32 D) = 2^(64 n)` and `m' = -m⁻¹ mod
2³²` (the low half of `M.minv`):

* `mul acc`: `[o] = [a] [b] R⁻¹ mod m`, by coarsely integrated operand
  scanning (CIOS) on digits, with the accumulator in memory: `2D + 2`
  digits at `[acc]`, cleared, and a window of them at `[r7]`, `r7` starting
  at `r3 + acc`. Each of the `D` iterations of the loop (counted down in
  `r8`; `r5` points to digit `i` of `[a]`) does two rows: the window
  `+= u [b]` (`mulRow`, `u` in `r9`), then `+= q m` for `q = t₀ m' mod 2³²`,
  which clears the window's low digit, and the window moves up a digit
  (`r7 += 4`) instead of shifting the accumulator. Its last `D + 1` digits
  are then below `2m` and reduced by `csub`.
* `add acc`: the digits of `[a] + [b]` at `[acc]`, then `csub`; `sub acc`:
  the digits of `[a] + m - [b]` (each digit `a_j + m_j + (2³² - 1 - b_j)`
  plus the carry, from a carry of 1, which adds `2^(32 D)`, taken off the
  top digit), then `csub`.
* `csub src`: the number below `2m` at `[src]` (`D` digits and a top digit,
  0 or 1) reduced modulo `m` into `[o]`: the digits of its difference with
  `m` (each `t_j + (2³² - 1 - m_j)` plus the carry, from 1) are stored in
  `[M.tmp]`; the carry out plus the top digit is 1 if it did not borrow, and
  its negation selects the difference or the number, a 64-bit word at a time.

Every multiplication is `mulld` of numbers below `2³²`, every selection a
mask, and every address `r3`, `r4`, `r5`, `r6` or `r7` (`r3` plus a multiple
of 4 counted by the loop, for `r5` and `r7`) plus a constant: nothing but
the pointers may affect timing. The operations use `r0` and `r5`–`r12`, and
write only `[o]`, `[acc]` and `[M.tmp]`.
-/

@[expose] public section

namespace VG.Impl.Mont.PPC64LE

open VG.PPC64LE

/-- The working space's base. -/
abbrev wb : Reg := .r3

/-- The number of 32-bit digits of a number. -/
def digits (M : Mod) : Nat := 2 * M.n

/-- `-m⁻¹ mod 2³²`. -/
def minv32 (M : Mod) : BitVec 32 := M.minv.setWidth 32

/-- `d = x`, a 32-bit constant, sign-extended (`lis`, `ori`): its low 32
bits are `x`. -/
def movImm (d : Reg) (x : BitVec 32) : List Instr :=
  [.lis d (x.extractLsb' 16 16), .ori d d (x.extractLsb' 0 16)]

/-- `[r7 + 4j] += r9 · [rs + src + 4j] + r10`, its low digit kept and its
carry to `r10` (a multiply-accumulate step, which never overflows). -/
def mulStep (rs : Reg) (src j : Nat) : List Instr :=
  [.load .w .r11 rs (src + 4 * j), .load .w .r12 .r7 (4 * j), .mul .r11 .r9 .r11,
    .add .r12 .r12 .r11, .add .r12 .r12 .r10, .store .w .r12 .r7 (4 * j), .lsr .d .r10 .r12 32]

/-- The carry `r10` added into the window's digits `D` and `D + 1`. -/
def carryUp (D : Nat) : List Instr :=
  [.load .w .r12 .r7 (4 * D), .add .r12 .r12 .r10, .store .w .r12 .r7 (4 * D), .lsr .d .r12 .r12 32,
    .load .w .r11 .r7 (4 * D + 4), .add .r11 .r11 .r12, .store .w .r11 .r7 (4 * D + 4)]

/-- The window `+= r9 · [rs + src]`, `D` digits, with its carry. -/
def mulRow (rs : Reg) (src D : Nat) : List Instr :=
  .li .r10 0 :: (List.range D).flatMap (mulStep rs src) ++ carryUp D

/-- An iteration of `mul`: the row for digit `r5` of `[a]` (`[b]` at `r6`),
then the row for `q = t₀ m' mod 2³²` (the modulus at `[r3 + M.mo]`), then
the window and `r5` up a digit, and the count. -/
def row (M : Mod) : List Instr :=
  [.load .w .r9 .r5 0] ++ mulRow .r6 0 (digits M) ++
  ([.load .w .r9 .r7 0] : List Instr) ++ movImm .r0 (minv32 M) ++
  ([.mul .r9 .r9 .r0, .rotr .w .r9 .r9 0] : List Instr) ++ mulRow wb M.mo (digits M) ++
  ([.addi .r7 .r7 4, .addi .r5 .r5 4, .subi .r8 .r8 1] : List Instr)

/-- `[r3 + acc]`, `k` digits, cleared (through `r11`). -/
def zeros (acc k : Nat) : List Instr :=
  .li .r11 0 :: (List.range k).map fun j => .store .w .r11 wb (acc + 4 * j)

/-- `r0 = 2³² - 1`. -/
def mask32 : List Instr := [.li .r0 0, .ori .r0 .r0 0xffff, .oris .r0 .r0 0xffff]

/-- Digit `j` of `[r3 + src] - m`, from the carry `r10` (1 for the first),
stored at `[r3 + M.tmp + 4j]`, its carry to `r10`. -/
def diffDigit (M : Mod) (src j : Nat) : List Instr :=
  [.load .w .r11 wb (src + 4 * j), .load .w .r12 wb (M.mo + 4 * j), .add .r11 .r11 .r0,
    .sub .r11 .r11 .r12, .add .r11 .r11 .r10, .store .w .r11 wb (M.tmp + 4 * j), .lsr .d .r10 .r11 32]

/-- Word `k` of the number at `[r3 + src]`, or of `[r3 + M.tmp]` where the
mask `r10` is all ones, to `[r4 + 8k]`. -/
def selWord (M : Mod) (src k : Nat) : List Instr :=
  [.load .d .r11 wb (src + 8 * k), .load .d .r12 wb (M.tmp + 8 * k), .logic .xor .r12 .r12 .r11,
    .logic .and .r12 .r12 .r10, .logic .xor .r11 .r11 .r12, .store .d .r11 .r4 (8 * k)]

/-- The number at `[r3 + src]` (`D` digits, then a top digit 0 or 1), below
`2m`, reduced modulo `m` into `[r4]`: the difference with `m` to `[M.tmp]`;
`r10` is 1 if it did not borrow, and its negation selects it. -/
def csub (M : Mod) (src : Nat) : List Instr :=
  mask32 ++ [.li .r10 1] ++ (List.range (digits M)).flatMap (diffDigit M src) ++
  ([.load .w .r11 wb (src + 4 * digits M), .add .r10 .r10 .r11, .li .r11 0,
    .sub .r10 .r11 .r10] : List Instr) ++
  (List.range M.n).flatMap (selWord M src)

/-- `[r4] = [r5] [r6] R⁻¹ mod m`, through the accumulator at `[r3 + acc]`
(`[r4]` may be `[r5]` or `[r6]`). -/
def mul (M : Mod) (acc : Nat) : Prog isa :=
  .seq (.block (zeros acc (2 * digits M + 2) ++ [.addi .r7 wb acc, .li .r8 (digits M)])) <|
  .seq (.loop (.block (row M)) (.nonzero .d .r8)) <|
    .block (csub M (acc + 4 * digits M))

/-- Digit `j` of `[r5] + [r6]`, from the carry `r10`, to `[r3 + acc]`, its
carry to `r10`. -/
def addDigit (acc j : Nat) : List Instr :=
  [.load .w .r11 .r5 (4 * j), .load .w .r12 .r6 (4 * j), .add .r11 .r11 .r12, .add .r11 .r11 .r10,
    .store .w .r11 wb (acc + 4 * j), .lsr .d .r10 .r11 32]

/-- `[r4] = [r5] + [r6] mod m`. -/
def add (M : Mod) (acc : Nat) : List Instr :=
  [.li .r10 0] ++ (List.range (digits M)).flatMap (addDigit acc) ++
  ([.store .w .r10 wb (acc + 4 * digits M)] : List Instr) ++ csub M acc

/-- Digit `j` of `[r5] + m - [r6]` (`r0 = 2³² - 1`), from the carry `r10`,
to `[r3 + acc]`, its carry to `r10`. -/
def subDigit (M : Mod) (acc j : Nat) : List Instr :=
  [.load .w .r11 .r5 (4 * j), .load .w .r12 wb (M.mo + 4 * j), .add .r11 .r11 .r12, .add .r11 .r11 .r0,
    .load .w .r12 .r6 (4 * j), .sub .r11 .r11 .r12, .add .r11 .r11 .r10,
    .store .w .r11 wb (acc + 4 * j), .lsr .d .r10 .r11 32]

/-- `[r4] = [r5] - [r6] mod m`, as `[r5] + m - [r6]` reduced. -/
def sub (M : Mod) (acc : Nat) : List Instr :=
  mask32 ++ [.li .r10 1] ++ (List.range (digits M)).flatMap (subDigit M acc) ++
  ([.subi .r10 .r10 1, .store .w .r10 wb (acc + 4 * digits M)] : List Instr) ++ csub M acc

/-- `[r3 + o] = x`, `n` 64-bit words, as `2n` 32-bit words through `r11`. -/
def setConst (n : Nat) (o x : Nat) : List Instr :=
  (List.range (2 * n)).flatMap fun j =>
    movImm .r11 (BitVec.ofNat 32 (x >>> (32 * j))) ++ ([.store .w .r11 wb (o + 4 * j)] : List Instr)

end VG.Impl.Mont.PPC64LE
