import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Impl.Mont.Mod

/-!
# Montgomery arithmetic modulo an odd multiword modulus, on AArch64

Arithmetic modulo an odd `m < 2^(64 n)`, `n` 64-bit words (`n ≤ 6`), on
numbers below `m` held in the working space as `n` little-endian words at a
constant offset from its base, which is in `x0`. The modulus is in the
working space too, at `M.mo`; `M.minv` is `-m⁻¹ mod 2⁶⁴`. With
`R = 2^(64 n)`:

* `mul o a b`: `[o] = [a] [b] R⁻¹ mod m`, by coarsely integrated operand
  scanning (CIOS): for each word `a_i` of `[a]`, the accumulator
  `t += a_i [b]`, then `t += u m` for `u = t₀ m' mod 2⁶⁴`, which makes the
  low word zero, and `t /= 2⁶⁴`. The `n + 2` accumulator words are
  registers (`acc n`); the division renames them (round `i`'s words are
  `win n i 0`, `win n i 1`, …), so it costs nothing. The accumulator stays
  below `2m`, and the result is reduced by `csub`.
* `add o a b`, `sub o a b`: `[a] ± [b] mod m`, with a conditional
  subtraction (`csub`) or addition of `m`.
* `csub`: a number below `2m` in `n` registers and a top word (0 or 1)
  reduced below `m`: the difference with `m` is computed into the
  temporary area `[M.tmp]`, and then selected with a mask if it did not
  borrow.

A product is `mul` and `umulh`, the carries are `adds`, `adcs` and `adc`
(with `x7 = 0`), every selection is a mask, and every address is `x0` plus
a constant: nothing but `x0` may affect timing. The operations use the
registers `x1`–`x7`, `x16`, `x17` and `acc n` (`x8`–`x13` for `n = 4`), and
write only `[o]` and `[M.tmp]`.
-/

namespace VG.Impl.Mont.AArch64

open VG.AArch64 VG.Impl.Mont

/-- `t = [x0 + d]`. -/
def ld (t : Reg) (d : Nat) : Instr := .ldr .x t .x0 d

/-- `[x0 + d] = t`. -/
def st (t : Reg) (d : Nat) : Instr := .str .x t .x0 d

/-- `r = v`, by `movz` and three `movk`s. -/
def const64 (r : Reg) (v : BitVec 64) : List Instr :=
  [.movz .x r (v.extractLsb' 0 16) 0, .movk .x r (v.extractLsb' 16 16) 1,
    .movk .x r (v.extractLsb' 32 16) 2, .movk .x r (v.extractLsb' 48 16) 3]

/-- `x7 = 0`, for the carries. -/
def zero7 : Instr := .movz .x .x7 0 0

/-- The accumulator's registers: `n + 2` of `x8`–`x15`. -/
def acc (n : Nat) : List Reg := [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15].take (n + 2)

/-- Word `j` of the accumulator in round `i`: the registers rotate by one
word each round. -/
def win (n i j : Nat) : Reg := (acc n).getD ((i + j) % (n + 2)) .x8

/-- `t:c = t + c + a · b` (a multiply-accumulate step; it never overflows),
through `x3` and `x4`, with `x7 = 0`. -/
def mulStep (t c a b : Reg) : List Instr :=
  [.mul .x .x3 a b, .umulh .x4 a b, .adds .x .x3 .x3 c, .adc .x .x4 .x4 .x7,
    .adds .x t t .x3, .adc .x c .x4 .x7]

/-- `ts, carry x5 += x1 · [d], …`: a multiply-accumulate step for each of
the words `ts` and the words at `d`, `d + 8`, …, each loaded into `x2`. -/
def mulSteps : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, d => ld .x2 d :: mulStep t .x5 .x1 .x2 ++ mulSteps ts (d + 8)

/-- `ts += x1 · [d]`, its carry word in `x5`. -/
def mulRow (ts : List Reg) (d : Nat) : List Instr := .movz .x .x5 0 0 :: mulSteps ts d

/-- The carry word `x5` added into `t_n` and its carry into `t_{n+1}`. -/
def carryUp (tn tn1 : Reg) : List Instr := [.adds .x tn tn .x5, .adc .x tn1 tn1 .x7]

/-- The words of round `i`'s accumulator, low to high. -/
def wins (n i : Nat) : List Reg := (List.range (n + 2)).map (win n i)

/-- Round `i` of `mul o a b`: `t += a_i [b]`, then `t += u m` with
`u = t₀ m' mod 2⁶⁴` (in `x1`, with `m'` in `x6`), after which `t₀ = 0`. -/
def round (M : Mod) (a b i : Nat) : List Instr :=
  let t := win M.n i
  let low := (List.range M.n).map t
  [ld .x1 (a + 8 * i)] ++ mulRow low b ++ carryUp (t M.n) (t (M.n + 1)) ++
  const64 .x6 M.minv ++ [.mul .x .x1 (t 0) .x6] ++
    mulRow low M.mo ++ carryUp (t M.n) (t (M.n + 1))

/-- `[tmp + d] = ts - [mo + d]`, word by word, with `subs` on the first word
and `sbcs` on the others, through `x2` and `x16`. -/
def diffs (first : Bool) : List Reg → Nat → Nat → List Instr
  | [], _, _ => []
  | t :: ts, mo, tmp =>
    [ld .x2 mo, if first then .subs .x .x16 t .x2 else .sbcs .x .x16 t .x2, st .x16 tmp] ++
      diffs false ts (mo + 8) (tmp + 8)

/-- `ts = [tmp]` where the mask `x17` is zero, word by word, through `x2`
and `x16`. -/
def selects : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, tmp => [ld .x16 tmp, .logic .eor .x .x2 t .x16, .logic .and .x .x2 .x2 .x17,
      .logic .eor .x t .x16 .x2] ++ selects ts (tmp + 8)

/-- `ts` (and the top word `top`), below `2m`, reduced modulo `m`: the
difference with `m` is computed into `[tmp]`; `x17` is all ones if it
borrowed (`sbc` of zeros, with `x7 = 0`), and selects the difference
where it is zero. -/
def csub (M : Mod) (ts : List Reg) (top : Reg) : List Instr :=
  diffs true ts M.mo M.tmp ++ [.sbcs .x .x16 top .x7, .sbc .x .x17 .x7 .x7] ++ selects ts M.tmp

/-- `[o] = ts`. -/
def stores : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, o => st t o :: stores ts (o + 8)

/-- `ts = [a]`. -/
def loads : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, a => ld t a :: loads ts (a + 8)

/-- `ts := 0`. -/
def zeros (ts : List Reg) : List Instr := ts.map fun t => .movz .x t 0 0

/-- `[o] = [a] [b] R⁻¹ mod m` (`o` may be `a` or `b`). -/
def mul (M : Mod) (o a b : Nat) : List Instr :=
  let low := (List.range M.n).map (win M.n M.n)
  zero7 :: zeros (acc M.n) ++ (List.range M.n).flatMap (round M a b) ++
    csub M low (win M.n M.n M.n) ++ stores low o

/-- `ts op= [b]`, word by word through `x2`, with `op` on the first word and
`op'` on the others (`adds` and `adcs`, `subs` and `sbcs`). -/
def chain (op op' : Reg → Reg → Reg → Instr) : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, b => [ld .x2 b, op t t .x2] ++ chain op' op' ts (b + 8)

/-- The low words and the top word of the sums and differences. -/
def low (n : Nat) : List Reg := (acc n).take n
def top (n : Nat) : Reg := (acc n).getD n .x8

/-- `[o] = [a] + [b] mod m`. -/
def add (M : Mod) (o a b : Nat) : List Instr :=
  zero7 :: loads (low M.n) a ++ chain (.adds .x) (.adcs .x) (low M.n) b ++
    [.adc .x (top M.n) .x7 .x7] ++ csub M (low M.n) (top M.n) ++ stores (low M.n) o

/-- `ts += [mo]` masked with `x17`, word by word through `x2`. -/
def addMasked (first : Bool) : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, mo => [ld .x2 mo, .logic .and .x .x2 .x2 .x17,
      if first then .adds .x t t .x2 else .adcs .x t t .x2] ++ addMasked false ts (mo + 8)

/-- `[o] = [a] - [b] mod m`: the difference, and `m` added under the mask
`x17` of its borrow. -/
def sub (M : Mod) (o a b : Nat) : List Instr :=
  zero7 :: loads (low M.n) a ++ chain (.subs .x) (.sbcs .x) (low M.n) b ++
    [.sbc .x .x17 .x7 .x7] ++ addMasked true (low M.n) M.mo ++ stores (low M.n) o

end VG.Impl.Mont.AArch64
