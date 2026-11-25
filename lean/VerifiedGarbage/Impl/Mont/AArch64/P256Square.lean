module

public import VerifiedGarbage.Impl.Mont.AArch64

/-!
# Montgomery squaring modulo P-256's prime, on AArch64

`square M o a`: `[o] = [a]² R⁻¹ mod p`, `R = 2²⁵⁶`,
`p = 2²⁵⁶ - 2²²⁴ + 2¹⁹² + 2⁹⁶ - 1`, with `x0`'s working space and the
registers of `mul`.

The products `aᵢ aⱼ`, `i < j`, are summed as three numbers whose words do not
overlap: `a₀a₁`, `a₀a₃`, `a₂a₃` side by side, `a₀a₂` and `a₁a₃` side by side,
and `a₁a₂` (`crossAdd`). The sum is doubled and the squares are added
(`diagonalAdd`), which gives `t₀, …, t₇`.

The reduction adds `q p`, `q = -t p⁻¹ mod R`, whose words are found low to
high. As `q p = q 2²⁵⁶ - q 2²²⁴ + q 2¹⁹² + q 2⁹⁶ - q`, adding `q 2⁹⁶` to the
low words of `t` gives `q` itself (`quotient`), but for its top word, which
also has `q₀ (2¹⁹² - 2²²⁴)`. With `s = ⌊q / 2³²⌋`, whose words are
`extr`s of `q`'s (the lowest, also of `t`'s: `q₁` and `t₁` agree in their low
halves), the low words of `t + q 2⁹⁶ - q` cancel, and what is left is
`⌊t / R⌋ + ⌊q / 2¹⁶⁰⌋ + (q - s) + ⌊q / 2⁶⁴⌋` and the three carries of `q₃`,
each of which starts one chain of additions (`addTop`, `subShift`, `addShift`).
-/

@[expose] public section

namespace VG.Impl.Mont.AArch64.P256Square

open VG.AArch64

/-- `M` is P-256's prime. -/
def supported (M : Mod) : Bool :=
  M.n == 4 && decide (M.red = Red.ofModulus 4
    0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)

/-- The operand's words. -/
def operand : List Reg := [.x3, .x4, .x5, .x6]

/-- `x8`–`x13`: the sum of `aᵢ aⱼ 2^(64 (i + j - 1))` over `i < j`. -/
def crossMul : List Instr :=
  [.mul .x .x8 .x3 .x4, .umulh .x9 .x3 .x4, .mul .x .x1 .x3 .x5, .umulh .x2 .x3 .x5,
   .mul .x .x10 .x3 .x6, .umulh .x11 .x3 .x6, .mul .x .x16 .x4 .x5, .umulh .x17 .x4 .x5,
   .mul .x .x14 .x4 .x6, .umulh .x15 .x4 .x6, .mul .x .x12 .x5 .x6, .umulh .x13 .x5 .x6]

def crossAdd : List Instr :=
  [.adds .x .x9 .x9 .x1, .adcs .x .x10 .x10 .x2, .adcs .x .x11 .x11 .x14,
   .adcs .x .x12 .x12 .x15, .adc .x .x13 .x13 .x7]

def crossAdd' : List Instr :=
  [.adds .x .x10 .x10 .x16, .adcs .x .x11 .x11 .x17, .adcs .x .x12 .x12 .x7, .adc .x .x13 .x13 .x7]

/-- Twice `x8`–`x13`, with the top bit in `x14`. -/
def double : List Instr :=
  [.adds .x .x8 .x8 .x8, .adcs .x .x9 .x9 .x9, .adcs .x .x10 .x10 .x10, .adcs .x .x11 .x11 .x11,
   .adcs .x .x12 .x12 .x12, .adcs .x .x13 .x13 .x13, .adc .x .x14 .x7 .x7]

/-- The squares `aᵢ²`. -/
def diagonalMul : List Instr :=
  [.mul .x .x15 .x3 .x3, .umulh .x1 .x3 .x3, .mul .x .x2 .x4 .x4, .umulh .x16 .x4 .x4,
   .mul .x .x17 .x5 .x5, .umulh .x3 .x5 .x5, .mul .x .x4 .x6 .x6, .umulh .x6 .x6 .x6]

/-- The square, in `x15`, `x8`–`x14`. -/
def diagonalAdd : List Instr :=
  [.adds .x .x8 .x8 .x1, .adcs .x .x9 .x9 .x2, .adcs .x .x10 .x10 .x16, .adcs .x .x11 .x11 .x17,
   .adcs .x .x12 .x12 .x3, .adcs .x .x13 .x13 .x4, .adc .x .x14 .x14 .x6]

/-- `q`, in `x15`, `x8`, `x9`, `x5`, and the words of `s = ⌊q / 2³²⌋` in `x2`,
`x3`, `x6`, `x16`. `x10` and `x4` are the summands of `q₃`, `x1` is `2³² q₀`,
and the carry flag is that of `x10`. -/
def quotient : List Instr :=
  [.lsl .x .x1 .x15 32, .sub .x .x4 .x15 .x1, .extr .x .x2 .x8 .x15 32, .adds .x .x8 .x8 .x1,
   .adcs .x .x9 .x9 .x2, .extr .x .x3 .x9 .x8 32, .adcs .x .x10 .x10 .x3,
   .add .x .x5 .x10 .x4, .extr .x .x6 .x5 .x9 32, .lsr .x .x16 .x5 32]

/-- `x11`–`x14` `+= ⌊q / 2¹⁶⁰⌋` and the carry of `x10`. -/
def addTop : List Instr :=
  [.adcs .x .x11 .x11 .x6, .adcs .x .x12 .x12 .x16, .adcs .x .x13 .x13 .x7, .adc .x .x14 .x14 .x7]

/-- `x15`, `x2`, `x3`, `x1` `= q - s`, less the borrow of `x4`. -/
def subShift : List Instr :=
  [.subs .x .x1 .x15 .x1, .sbcs .x .x15 .x15 .x2, .sbcs .x .x2 .x8 .x3, .sbcs .x .x3 .x9 .x6,
   .sbc .x .x1 .x5 .x16]

/-- `x15`, `x2`, `x3`, `x1` `+= ⌊q / 2⁶⁴⌋` and the carry of `x5`. -/
def addShift : List Instr :=
  [.adds .x .x4 .x10 .x4, .adcs .x .x15 .x15 .x8, .adcs .x .x2 .x2 .x9, .adcs .x .x3 .x3 .x5,
   .adc .x .x1 .x1 .x7]

/-- The reduced square, below `2p`, in `x8`–`x11` and the top bit `x12`. -/
def sum : List Instr :=
  [.adds .x .x8 .x11 .x15, .adcs .x .x9 .x12 .x2, .adcs .x .x10 .x13 .x3, .adcs .x .x11 .x14 .x1,
   .adc .x .x12 .x7 .x7]

/-- The square `[a]² R⁻¹`, below `2p`, in `x8`–`x11` and the top bit `x12`, with `x7 = 0`. -/
def core (a : Nat) : List Instr :=
  zero7 :: loads operand a ++ (crossMul ++ crossAdd ++ crossAdd' ++ double ++ diagonalMul ++
    diagonalAdd ++ quotient ++ addTop ++ subShift ++ addShift ++ sum)

/-- The registers of the result of `core`. -/
def result : List Reg := [.x8, .x9, .x10, .x11]

/-- `[o] = [a]² R⁻¹ mod p` (`o` may be `a`). -/
def square (M : Mod) (o a : Nat) : List Instr :=
  core a ++ (csubR M result .x12 ++ stores result o)

end VG.Impl.Mont.AArch64.P256Square
