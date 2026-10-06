import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Impl.Bignum.Layout

/-!
# Multiword arithmetic on AArch64: the baseline

Numbers of `w` 64-bit words, little-endian, in arrays in the working space,
for a `w` known only at run time, with the layout of `Impl/Bignum/Layout.lean`
(the same as on x86-64): a header of 32 words, then eight arrays of `w + 2`
words. Every loop runs over the words of an array, counting down a register
from a public count with `cbnz`, and every address is an array's base, from
the header, plus 8 times a counter: only `w` and the bases may affect timing.

The working space's base is in `x0`.

* `montMul o a b`: `[o] = [a] [b] R⁻¹ mod m` for `R = 2^(64 w)`, by
  coarsely integrated operand scanning (CIOS), with the accumulator
  (`w + 2` words) in memory, then a subtraction of `m` whose carry selects
  the result with `csel`. `o` may be `a` or `b`. The arrays are given by
  the header slots of their bases.
* `double o`: `[o] = 2 [o] mod m`.
* `loadBE`, `storeBE`: an array from and to big-endian bytes.

The model has no register-offset addressing, so a loop walks pointers to
the words it reads and writes, each advanced by 8 per word. The carry
chains of additions and subtractions keep their carry in the carry flag
from one word to the next: the counters (`add`, `sub` with an immediate),
loads, stores and `cbnz` leave it alone.

The registers: `x0` the working space; `x8` the accumulator, `x9` `b`, `x10`
`m`, `x11` (advancing over) `a`; `x12` `w`; `x13`, `x14` counters; `x15`
`-m⁻¹`; `x1` a word of `a` or the multiple `u` of `m`; `x2` a carry; `x7`
zero; `x3`–`x6`, `x16`, `x17` temporaries and pointers. No callee-saved
register is written.
-/

namespace VG.Impl.Bignum.AArch64

open VG.AArch64 VG.Impl.Bignum

/-- `t = [n + off]`, a word. -/
def ld (t n : Reg) (off : Nat := 0) : Instr := .ldr .x t n off

/-- `[n + off] = t`, a word. -/
def st (t n : Reg) (off : Nat := 0) : Instr := .str .x t n off

/-- `t = header slot i`. -/
def ldh (t : Reg) (i : Nat) : Instr := .ldr .x t .x0 (8 * i)

/-- `header slot i = t`. -/
def sth (t : Reg) (i : Nat) : Instr := .str .x t .x0 (8 * i)

/-- `d = n`. -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- `d = imm` (`imm < 2¹⁶`). -/
def movi (d : Reg) (imm : Nat) : Instr := .movz .x d (BitVec.ofNat 16 imm) 0

/-- `p += 8`: the next word. -/
def next (p : Reg) : Instr := .addImm .x p p 8

/-- `do body; cnt -= 1 while cnt ≠ 0`, for `cnt` at least 1. -/
def countLoop (cnt : Reg) (body : List Instr) : Prog isa :=
  .loop (.block (body ++ [.subImm .x cnt cnt 1])) (.nonzero .x cnt)

/-! ## Montgomery multiplication -/

/-- Load `x8` (the accumulator), `x9` (`b`), `x10` (`m`), `x11` (`a`), `x5`
(`o`), `x6` (`tmp`), `x12` (`w`) and `x15` (`-m⁻¹`) from the header, and
`x7 := 0`. All loads from the header come before any store of a secret, so
the bases stay public to the taint analysis. -/
def bases (o a b mo acc tmp : Nat) : List Instr :=
  [ldh .x8 (sArr acc), ldh .x9 (sArr b), ldh .x10 (sArr mo), ldh .x11 (sArr a), ldh .x5 (sArr o),
    ldh .x6 (sArr tmp), ldh .x12 sW, ldh .x15 sMinv, movi .x7 0]

/-- The `w + 2` words of the accumulator := 0. -/
def zeroAcc : Prog isa :=
  .seq (.block [mov .x16 .x8, .addImm .x .x14 .x12 2])
    (countLoop .x14 [st .x7 .x16, next .x16])

/-- A multiply-accumulate step: `x1 · [x17]` plus the carry `x2` plus the
accumulator's word, its low word stored at `x16` and its high word the new
carry; then both pointers advanced. The accumulator's word is at `x16`, or
at `x16 + 8` for the reduction (`down`), which stores one word down. -/
def mac (down : Bool) : List Instr :=
  [ld .x3 .x17, .mul .x .x4 .x1 .x3, .umulh .x3 .x1 .x3, .adds .x .x4 .x4 .x2, .adc .x .x3 .x3 .x7,
    ld .x2 .x16 (if down then 8 else 0), .adds .x .x4 .x4 .x2, .adc .x .x2 .x3 .x7, st .x4 .x16,
    next .x16, next .x17]

/-- Words `w` and `w + 1` of the accumulator (at `x16`) `+= x2`. -/
def rowTop : List Instr :=
  [ld .x3 .x16, .adds .x .x3 .x3 .x2, st .x3 .x16, ld .x3 .x16 8, .adc .x .x3 .x3 .x7, st .x3 .x16 8]

/-- `acc += x1 · [b]`: `w` steps over `b`, then the last carry into words `w`
and `w + 1`. -/
def mulAddRow : Prog isa :=
  .seq (.block [mov .x16 .x8, mov .x17 .x9, mov .x14 .x12, movi .x2 0])
    (.seq (countLoop .x14 (mac false)) (.block rowTop))

/-- `u = acc₀ · (-m⁻¹) mod 2⁶⁴` into `x1`, and the carry of `acc₀ + u m₀`
(whose low word is zero) into `x2`; `x16` at the accumulator, `x17` at
`m₁` and `x14 := w - 1`. -/
def redHead : List Instr :=
  [ld .x3 .x8, .mul .x .x1 .x3 .x15, ld .x4 .x10, .mul .x .x2 .x1 .x4, .umulh .x4 .x1 .x4,
    .adds .x .x2 .x2 .x3, .adc .x .x2 .x4 .x7, mov .x16 .x8, .addImm .x .x17 .x10 8,
    .subImm .x .x14 .x12 1]

/-- Words `w` and `w + 1` of the accumulator plus the carry, stored one word
down, and word `w + 1` zeroed (`x16` at word `w - 1`). -/
def redTop : List Instr :=
  [ld .x3 .x16 8, .adds .x .x3 .x3 .x2, st .x3 .x16, ld .x3 .x16 16, .adc .x .x3 .x3 .x7,
    st .x3 .x16 8, st .x7 .x16 16]

/-- `acc := (acc + u m) / 2⁶⁴` for `u = acc₀ · (-m⁻¹) mod 2⁶⁴`, which makes the
low word zero: word 0, then words 1 to `w - 1` each stored one word down,
then the top words. -/
def reduceRow : Prog isa :=
  .seq (.block redHead) (.seq (countLoop .x14 (mac true)) (.block redTop))

/-- One round: `x1 := a_i` (`x11` advanced), the row of `a_i b`, the
reduction. -/
def round : Prog isa :=
  .seq (.block [ld .x1 .x11, next .x11]) (.seq mulAddRow reduceRow)

/-- The `w` rounds, counted by `x13`. -/
def rounds : Prog isa :=
  .seq (.block [mov .x13 .x12])
    (.loop (.seq round (.block [.subImm .x .x13 .x13 1])) (.nonzero .x .x13))

/-- `[tmp] = acc - m` over `w` words (`tmp` at `x6`), then the carry flag
set iff `acc ≥ m`, counting the top word `w` of `acc`: a chain of `sbcs`
from the carry set (no borrow). -/
def subMod : Prog isa :=
  .seq (.block [mov .x16 .x8, mov .x17 .x10, mov .x13 .x6, mov .x14 .x12, .subs .x .x3 .x7 .x7])
    (.seq (countLoop .x14 [ld .x3 .x16, ld .x4 .x17, .sbcs .x .x3 .x3 .x4, st .x3 .x13, next .x16,
        next .x17, next .x13])
      (.block [ld .x3 .x16, .sbcs .x .x3 .x3 .x7]))

/-- `[o] = carry ? [tmp] : acc`, word by word (`o` at `x5`, `tmp` at `x6`). -/
def selectAcc : Prog isa :=
  .seq (.block [mov .x16 .x8, mov .x14 .x12])
    (countLoop .x14 [ld .x3 .x16, ld .x4 .x6, .csel .x .x3 .x4 .x3, st .x3 .x5, next .x16, next .x6,
      next .x5])

/-- `[o] = [a] [b] R⁻¹ mod m`, with the accumulator at array `acc` and the
temporary array `tmp`; `m` is array `mo`. -/
def montMul (mo acc tmp o a b : Nat) : Prog isa :=
  .seq (.block (bases o a b mo acc tmp)) (.seq zeroAcc (.seq rounds (.seq subMod selectAcc)))

/-- `[o] = 2 [o] mod m` for `[o] < m`: the double into the accumulator
(`w + 1` words, a chain of `adcs` from the carry clear), then the
subtraction of `m` selected as in `montMul`. -/
def double (mo acc tmp o : Nat) : Prog isa :=
  .seq (.block [ldh .x5 (sArr o), ldh .x10 (sArr mo), ldh .x8 (sArr acc), ldh .x6 (sArr tmp), ldh .x12 sW,
      movi .x7 0, mov .x17 .x5, mov .x16 .x8, mov .x14 .x12, .adds .x .x3 .x7 .x7])
    (.seq (countLoop .x14 [ld .x3 .x17, .adcs .x .x3 .x3 .x3, st .x3 .x16, next .x17, next .x16])
    (.seq (.block [.adc .x .x3 .x7 .x7, st .x3 .x16])
    (.seq subMod selectAcc)))

/-! ## Copies and comparisons -/

/-- `w` words (`x12`) from `[x16]` to `[x17]`, both advanced past them. -/
def copyWords : Prog isa :=
  .seq (.block [mov .x14 .x12]) (countLoop .x14 [ld .x3 .x16, st .x3 .x17, next .x16, next .x17])

/-- The borrow of `[x16] - [x17]` over `x14` words, from the carry flag set:
the carry flag ends clear iff `[x16] < [x17]`. -/
def cmpLoop : Prog isa :=
  countLoop .x14 [ld .x3 .x16, ld .x4 .x17, .sbcs .x .x3 .x3 .x4, next .x16, next .x17]

/-! ## Bytes and words -/

/-- The `k` bytes at `x1`, most significant first, into the `w` words of
the array at `x8` (`k` in `x2`, `w = ⌈k / 8⌉`): byte `i` is bit position
`8 p` for `p = k - 1 - i`, accumulated in `x3` (shifted left a byte per
byte) and stored as word `p / 8`, at `x8 + p`, when `p % 8 = 0`. `x2`
counts `p` down from `k`, and `x6 = 7`. -/
def loadBE : Prog isa :=
  .seq (.block [movi .x3 0, movi .x6 7])
    (.loop (.seq (.block [.subImm .x .x2 .x2 1, .lsl .x .x3 .x3 8, .ldrb .x4 .x1 0, .add .x .x3 .x3 .x4,
        .addImm .x .x1 .x1 1, .logic .and .x .x5 .x2 .x6])
      (.ite (.zero .x .x5) (.block [.add .x .x5 .x8 .x2, st .x3 .x5, movi .x3 0]) (.block [])))
      (.nonzero .x .x2))

/-- The low `k` bytes of the `w` words at `x8`, each and'ed with `x15`, to
the `k` bytes ending at `x1`, most significant first (`k` in `x9`): for `p`
from 0 to `k - 1` (in `x2`), byte `k - 1 - p` is the low byte of `x3`, which
is word `p / 8`, at `x8 + p` when `p % 8 = 0`, shifted right by
`8 (p % 8)`. `x9` counts down. -/
def storeBE : Prog isa :=
  .seq (.block [movi .x2 0, movi .x6 7])
    (.loop (.seq (.block [.logic .and .x .x5 .x2 .x6])
      (.seq (.ite (.zero .x .x5) (.block [.add .x .x5 .x8 .x2, ld .x3 .x5, .logic .and .x .x3 .x3 .x15]) (.block []))
        (.block [.subImm .x .x1 .x1 1, .strb .x3 .x1 0, .lsr .x .x3 .x3 8, .addImm .x .x2 .x2 1,
          .subImm .x .x9 .x9 1])))
      (.nonzero .x .x9))

/-- `c₁; c₂; …`. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-! ## Setting up -/

/-- The base of array `j` (in `x4`) into its slot, and `x4` advanced by
`x3` bytes. -/
def setBase (j : Nat) : List Instr := [sth .x4 (sArr j), .add .x .x4 .x4 .x3]

/-- The arrays' bases, `w + 2` words apart after the header, into slots
`sArr 0` to `sArr 7`; `w` in `x12`. -/
def setBases : List Instr :=
  [.addImm .x .x3 .x12 2, .lsl .x .x3 .x3 3, .addImm .x .x4 .x0 hdrBytes] ++ (List.range 8).flatMap setBase

/-- A step of Newton's iteration: `x4 := x4 (2 - x3 x4)`. -/
def newton : List Instr :=
  [.mul .x .x5 .x3 .x4, movi .x6 2, .sub .x .x5 .x6 .x5, .mul .x .x4 .x4 .x5]

/-- `-m⁻¹ mod 2⁶⁴` for the odd `m₀` in `x3`, into `x15`: Newton's iteration
`x ↦ x (2 - m₀ x)` five times from `x = m₀`, which is right modulo 8, then
the negation. -/
def minv : List Instr :=
  [mov .x4 .x3] ++ newton ++ newton ++ newton ++ newton ++ newton ++ [movi .x6 0, .sub .x .x15 .x6 .x4]

/-- `[o] := 0` but its word `i` (in `x13`), which is `x9`. `w` in `x12`. -/
def setWord (o : Nat) : Prog isa :=
  .seq (.block [ldh .x8 (sArr o), movi .x7 0]) (.seq zeroAcc
    (.block [.lsl .x .x16 .x13 3, .add .x .x16 .x8 .x16, st .x9 .x16]))

/-- `x9 := 2^j` and `x13 := 64 - j` for the top bit `j` of the nonzero `x3`:
`x3` is halved and `x9` doubled until `x3 = 1`. -/
def topBit : Prog isa :=
  .seq (.block [movi .x9 1, movi .x13 64, .subImm .x .x6 .x3 1])
    (.ite (.zero .x .x6) (.block [])
      (.loop (.block [.lsr .x .x3 .x3 1, .add .x .x9 .x9 .x9, .subImm .x .x13 .x13 1, .subImm .x .x6 .x3 1])
        (.nonzero .x .x6)))

/-- `double` `x13` times (a public count, at least 1), counted in a header
slot. -/
def doubles (mo acc tmp o slot : Nat) : Prog isa :=
  .seq (.block [sth .x13 slot])
    (.loop (.seq (double mo acc tmp o) (.block [ldh .x13 slot, .subImm .x .x13 .x13 1, sth .x13 slot]))
      (.nonzero .x .x13))

namespace Public

open VG.Impl.Bignum.Public

/-- `[o] = [a] [b] R⁻¹ mod m` in the working space of the public-key
operation: `m` in array `aN`, the accumulator `aAcc`, the temporary
`aTmp`. -/
def mm (o a b : Nat) : Prog isa := montMul aN aAcc aTmp o a b

end Public

end VG.Impl.Bignum.AArch64
