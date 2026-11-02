module

public import VerifiedGarbage.Impl.X25519.RISCV64.R64
public import VerifiedGarbage.Impl.Ed25519.RISCV64.MulFn
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P256Field

/-!
# Arithmetic modulo P-384's prime, as functions, on RISC-V

`vg_p384_{mul,add,sub}_mod_p(ws, o, a, b)` (`Proof/Weierstrass/MontContract.lean`;
`ws` in `a0`, the offsets in the low words of `a1`–`a3`), for
`p = 2³⁸⁴ - 2¹²⁸ - 2⁹⁶ + 2³² - 1`, numbers of six 64-bit words, as P-256's
(`Impl/Weierstrass/RISCV64/P256Field.lean`):

1. the offsets are zero-extended (`zext`), and `t2`, `t4` and `t5` point to
   `[o]`, `[a]` and `[b]`; `a3` is `ws + 2048`, which reaches the function's
   own working space (bytes 3712 to 4095 of `ws`, 1664 to 2047 from `a3`)
   with short offsets;
2. if the three pointers are multiples of 8 (`ws` is, so their offsets
   are), the operation runs on them (`core`); else the operands are copied a
   byte at a time into the own working space (`SA`, `SB`), the operation
   runs there with its result to `SO`, and the result is copied a byte at a
   time to `[o]`, whose pointer the copies keep in `t1`;
3. the operation:
   * `mulCore`: the operands copied to `MA` and `MB`, their twelve-word
     product at `ACC` by columns of `mul` and `mulhu` (X25519's terms,
     `Impl/X25519/RISCV64/R64.lean`, with six words of `b` in registers; its
     square, from `MA` alone, if the two pointers are equal: fifteen cross
     products rather than thirty-six), then Montgomery's reduction
     (`reduce`), which multiplies only by shifts. With `m = 2³⁸⁴ - p =
     2¹²⁸ + 2⁹⁶ - 2³² + 1`, the quotient word of the low word `w` is
     `q = w (2³² + 1) mod 2⁶⁴` (`-p⁻¹ ≡ 2³² + 1`), and adding `q p` is
     subtracting `q m` and adding `2³⁸⁴ q`: a round subtracts `q m` (whose
     low word is `w`; `qm` builds the three words above it), the borrow out
     of its top word left for the next round, and stores `q` in place of
     `w`; after six rounds, the last borrow is taken out of the top three
     words, the six quotient words are added to them, and the number, below
     `2p`, is `X` with its top bit `XC`, which `csub` reduces;
   * `addCore`: the sum with carries, then `csub`;
   * `subCore`: the difference with borrows, and `p` added back under the
     mask of the borrow.
   `csub`: the words of `x + (2³⁸⁴ - p)` with carries stored at `[t2]`;
   `x ≥ p` if and only if that or `x`'s top bit carries out of 384 bits,
   whose mask selects, word by word, the stored sum or `x`.

Every multiplication is `mul` or `mulhu`, every selection a mask, and the
only branches are on the pointers, which are public, as every address is a
pointer plus a constant. The functions use only caller-saved registers and
no stack, and write only `[o]` and their own working space.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.P384Field

open VG.RISCV64
open VG.Impl.X448.RISCV64.R64 (w rr macc zero3 ld6)
open VG.Impl.X25519.RISCV64.R64 (mulTerm colEnd sqTerm dblStep)

/-! ## Layout, from `a3 = ws + 2048` -/

/-- The copies of the operands, and the product's twelve words. -/
def MA : Nat := 1664
def MB : Nat := 1712
def ACC : Nat := 1760

/-- The byte-wise copies of the operands and the result, for offsets that
are not multiples of 8. -/
def SA : Nat := 1856
def SB : Nat := 1904
def SO : Nat := 1952

/-! ## Products of six words

X25519's (`Impl/X25519/RISCV64/R64.lean`), for six words: `b₀–b₅` in
`w 0`–`w 5` (`t3`–`t6`, `a1`, `a2`; X448's `ld6`), the accumulator of column
`k` in `rr k, rr (k + 1), rr (k + 2)`. -/

/-- The terms `(i, j)` of column `k` of a product of six words, `i`
descending. -/
def colPairs (k : Nat) : List (Nat × Nat) :=
  ((List.range 6).reverse.filter fun i => i ≤ k ∧ k - i < 6).map fun i => (i, k - i)

/-- Column `k` of `[a] · [b]`. -/
def mulCol (acc a k : Nat) : List Instr := (colPairs k).flatMap (mulTerm a k) ++ colEnd acc k

/-- The twelve words of `[a] · [b]` at `acc`. -/
def product (acc a b : Nat) : List Instr :=
  ld6 b ++ zero3 ++ (List.range 12).flatMap (mulCol acc a)

/-- Column `k` of the cross products of `[a]`. -/
def sqCol (acc k : Nat) : List Instr :=
  ((colPairs k).filter fun p => p.2 < p.1).flatMap (sqTerm k) ++ colEnd acc k

/-- The twelve words of `[a]²` at `acc`. -/
def square (acc a : Nat) : List Instr :=
  ld6 a ++ zero3 ++ (List.range 12).flatMap (sqCol acc) ++ [.li .a5 0, .li .a4 0] ++
    (List.range 12).flatMap (dblStep acc a)

/-! ## Entry -/

/-- The offsets zero-extended: only their low words are arguments (Ed25519's
`mulZext`). -/
abbrev zext : List Instr := Ed25519.RISCV64.mulZext

/-- `t2 = ws + o`, `t4 = ws + a`, `t5 = ws + b`, `a3 = ws + 2048`, and in `t0`
the low three bits of the pointers or'ed: P-256's. -/
abbrev ptrs : List Instr := P256Field.ptrs

/-! ## The final subtraction -/

/-- The result words of a reduction, a sum or a difference, `x₀`–`x₅`. -/
def XR : List Reg := [.t5, .t6, .t3, .t4, .a1, .a4]

def X (j : Nat) : Reg := XR.getD j .t5

/-- The top bit of a reduction or a sum. -/
def XC : Reg := .a2

/-- Word `j` of `x + N` into `a5`, stored at `[t2 + 8j]`: `N`'s word in `t0`,
the carry in and out in `a7`, through `a0`. -/
def sumWord (j : Nat) : List Instr :=
  [.add .a5 (X j) .t0, .sltu .a0 .a5 .t0, .add .a5 .a5 .a7, .sltu .a7 .a5 .a7, .add .a7 .a7 .a0,
    .store .d .a5 .t2 (8 * j)]

/-- `x + N` stored at `[t2]`, its carry into `a7`, for `N` whose word `j` is put
into `t0` by `ks[j]` (or kept there, for `[]`). -/
def sumWith (ks : List (List Instr)) : List Instr :=
  .li .a7 0 :: (List.range 6).flatMap fun j => ks.getD j [] ++ sumWord j

/-- The words of `2³⁸⁴ - p = [2⁶⁴ - 2³² + 1, 2³² - 1, 1, 0, 0, 0]` into `t0`. -/
def sumPKs : List (List Instr) :=
  [[.li .t0 (-1), .shift .sll .d .t0 .t0 32, .addi .t0 .t0 1],
    [.li .t0 (-1), .shift .srl .d .t0 .t0 32], [.li .t0 1], [.li .t0 0]]

/-- `x + (2³⁸⁴ - p)`. -/
def sumP : List Instr := sumWith sumPKs

/-- Word `j` of the result: the stored sum's if the mask `t0` is all ones,
else `x_j`'s, through `a5`. -/
def selWord (j : Nat) : List Instr :=
  [.load .d .a5 .t2 (8 * j), .logic .xor .a5 .a5 (X j), .logic .and .a5 .a5 .t0,
    .logic .xor .a5 .a5 (X j), .store .d .a5 .t2 (8 * j)]

/-- After a sum `x + (2³⁸⁴ - m)` stored at `[t2]` and its carry `a7`: the carry
or `XC` (`x ≥ m`) as a mask, which selects the sum or `x`. -/
def csubTail : List Instr :=
  [.logic .or .a7 .a7 XC, .li .t0 0, .sub .t0 .t0 .a7] ++ (List.range 6).flatMap selWord

/-- `x mod p` at `[t2]`, for the number `x = x₀ + … + 2³²⁰ x₅ + 2³⁸⁴ XC`
below `2p`. -/
def csub : List Instr := sumP ++ csubTail

/-! ## Montgomery's reduction -/

/-- The words of a round, rotating: round `i` reads `w = rw i` and subtracts
from `rw (i + 1)`–`rw (i + 3)`. -/
def RW : List Reg := [.t3, .t4, .t5, .t6]

def rw (i : Nat) : Reg := RW.getD (i % 4) .t3

/-- `q m / 2⁶⁴` for `q` in `r`, as `a4 + 2⁶⁴ a5 + 2¹²⁸ a6`: with
`q 2³² = l + 2⁶⁴ h` (`l = q << 32`, `h = q >> 32`) and `c = [q < l]`, it is
`(l - h - c) + 2⁶⁴ (q + h)`, whose low word may borrow (into `a7`), which `h`
covers; through `a7`. -/
def qm (r : Reg) : List Instr :=
  [.shift .sll .d .a4 r 32, .shift .srl .d .a5 r 32, .sltu .a6 r .a4, .add .a6 .a6 .a5,
    .sltu .a7 .a4 .a6, .sub .a4 .a4 .a6, .sub .a5 .a5 .a7, .add .a5 .a5 r, .sltu .a6 .a5 r]

/-- Round `i`: word `i + 3` of the product loaded, `w` in `rw i` replaced by
`q = w + (w << 32)` and stored at its word, then `q m / 2⁶⁴` and the borrow
`a2` of the round before subtracted from `rw (i + 1)`–`rw (i + 3)`, the
borrow out of them into `a2`. -/
def round (i : Nat) : List Instr :=
  [.load .d (rw (i + 3)) .a3 (ACC + 8 * (i + 3)), .shift .sll .d .t0 (rw i) 32,
    .add (rw i) (rw i) .t0, .store .d (rw i) .a3 (ACC + 8 * i)] ++ qm (rw i) ++
  [.sltu .a7 (rw (i + 1)) .a4, .sub (rw (i + 1)) (rw (i + 1)) .a4,
   .sltu .t0 (rw (i + 2)) .a5, .sub (rw (i + 2)) (rw (i + 2)) .a5, .sltu .a4 (rw (i + 2)) .a7,
   .sub (rw (i + 2)) (rw (i + 2)) .a7, .add .a7 .t0 .a4,
   .add .a6 .a6 .a2, .add .a6 .a6 .a7, .sltu .a2 (rw (i + 3)) .a6,
   .sub (rw (i + 3)) (rw (i + 3)) .a6]

/-- Word `j` of a sum into `d = d + y + c` (`c` in `a2`, in and out),
through `a6`. -/
def adcWord (d y : Reg) : List Instr :=
  [.add d d y, .sltu .a6 d y, .add d d .a2, .sltu .a2 d .a2, .add .a2 .a2 .a6]

/-- After the rounds: words 9 to 11 of the product loaded into `X 3`–`X 5`,
less the last borrow, which leaves the borrow `B` in `a5`; then the quotient
words at `ACC` added to `X 0`–`X 5` (words 6 to 11), and `XC` the carry
less `B`. -/
def finish : List Instr :=
  [.load .d (X 3) .a3 (ACC + 72), .load .d (X 4) .a3 (ACC + 80), .load .d (X 5) .a3 (ACC + 88),
   .sltu .a5 (X 3) .a2, .sub (X 3) (X 3) .a2, .sltu .a2 (X 4) .a5, .sub (X 4) (X 4) .a5,
   .sltu .a5 (X 5) .a2, .sub (X 5) (X 5) .a2, .li .a2 0] ++
  ((List.range 6).flatMap fun j => .load .d .a7 .a3 (ACC + 8 * j) :: adcWord (X j) .a7) ++
  [.sub XC XC .a5]

/-- The product at `ACC` reduced: its low three words loaded, the borrow
zero, the six rounds, which leave words 6 to 8 in `rw 6`–`rw 8` (`X 0`–`X 2`),
then `finish`. -/
def reduce : List Instr :=
  (List.range 3).map (fun j => .load .d (rw j) .a3 (ACC + 8 * j)) ++ [.li .a2 0] ++
    (List.range 6).flatMap round ++ finish

/-! ## The operations -/

/-- The six doublewords at `[p]` to `[a3 + o]`, through `t3`, `t6`, `a1`,
`a2`, `a4`, `a5`. -/
def copyIn (p : Reg) (o : Nat) : List Instr :=
  [.load .d .t3 p 0, .load .d .t6 p 8, .load .d .a1 p 16, .load .d .a2 p 24, .load .d .a4 p 32,
    .load .d .a5 p 40, .store .d .t3 .a3 o, .store .d .t6 .a3 (o + 8), .store .d .a1 .a3 (o + 16),
    .store .d .a2 .a3 (o + 24), .store .d .a4 .a3 (o + 32), .store .d .a5 .a3 (o + 40)]

/-- The product of `[t4]` and `[t5]` at `ACC`: a square if the pointers are equal. -/
def prodCode : Prog isa :=
  .ite (.eq .t4 .t5) (.block (copyIn .t4 MA ++ square ACC MA))
    (.block (copyIn .t4 MA ++ copyIn .t5 MB ++ product ACC MA MB))

/-- The product, reduced by `red` and `sum ++ csubTail`. -/
def mulWith (red sum : List Instr) : Prog isa := .seq prodCode (.block (red ++ (sum ++ csubTail)))

/-- `[t2] = [t4] [t5] R⁻¹ mod p`. -/
def mulCore : Prog isa := mulWith reduce sumP

/-- The pointers `t4` and `t5` copied to `a0` and `a7`, which the words of
`X` do not overwrite. -/
def movAB : List Instr := [.addi .a0 .t4 0, .addi .a7 .t5 0]

/-- The sum of `[a0]` and `[a7]` into `X 0`–`X 5` and `XC`, through `a5`, `a6`. -/
def addSum : List Instr :=
  movAB ++ .li .a2 0 :: (List.range 6).flatMap fun j =>
    [.load .d (X j) .a0 (8 * j), .load .d .a5 .a7 (8 * j)] ++ adcWord (X j) .a5

/-- `[t2] = [t4] + [t5] mod p`. -/
def addCore : List Instr := addSum ++ csub

/-- Word `j` of a difference into `d = d - y - c` (`c` in `a2`, in and out),
through `a6` and `t0`. -/
def sbbWord (d y : Reg) : List Instr :=
  [.sltu .a6 d y, .sub d d y, .sltu .t0 d .a2, .sub d d .a2, .add .a2 .a6 .t0]

/-- The difference of `[a0]` and `[a7]` into `X 0`–`X 5`, its borrow into `a2`. -/
def subDiff : List Instr :=
  movAB ++ .li .a2 0 :: (List.range 6).flatMap fun j =>
    [.load .d (X j) .a0 (8 * j), .load .d .a5 .a7 (8 * j)] ++ sbbWord (X j) .a5

/-- Word `j` of `x + (m ∧ M)` for the mask `M` in `t0` (`m`'s word under it in
`a6`), the carry in and out in `a7`, through `a0`, stored at `[t2 + 8j]`. -/
def addMWord (j : Nat) : List Instr :=
  [.add (X j) (X j) .a6, .sltu .a0 (X j) .a6, .add (X j) (X j) .a7, .sltu .a7 (X j) .a7,
    .add .a7 .a7 .a0, .store .d (X j) .t2 (8 * j)]

/-- `[t2] = [t4] - [t5] mod m`: the difference, then the borrow as a mask in
`t0`, and `m` under it added a word at a time, word `j` put into `a6` by
`ks[j]`. -/
def subWith (ks : List (List Instr)) : List Instr :=
  subDiff ++ [.li .t0 0, .sub .t0 .t0 .a2, .li .a7 0] ++
    (List.range 6).flatMap fun j => ks.getD j [] ++ addMWord j

/-- `p`'s words under the mask `M`: `M >> 32`, `M << 32`, `M << 1` and `M` three
times. -/
def subPKs : List (List Instr) :=
  [[.shift .srl .d .a6 .t0 32], [.shift .sll .d .a6 .t0 32], [.shift .sll .d .a6 .t0 1],
    [.addi .a6 .t0 0], [.addi .a6 .t0 0], [.addi .a6 .t0 0]]

/-- `[t2] = [t4] - [t5] mod p`. -/
def subCore : List Instr := subWith subPKs

/-! ## The functions -/

/-- The element at `a` (from `a3`) as the 48 bytes at `p` plus `dst`, a word
at a time. -/
def pack (p : Reg) (a dst : Nat) : List Instr :=
  (List.range 12).flatMap fun k => [.load .w .a4 .a3 (a + 4 * k)] ++ Words.RISCV64.storeLE32 .a4 .a5 p (dst + 4 * k)

/-- The 48 bytes at `p` plus `src` as the element at `o` (from `a3`). -/
def unpack (p : Reg) (o src : Nat) : List Instr :=
  (List.range 12).flatMap fun k => Words.RISCV64.loadLE32 .a4 .a5 p (src + 4 * k) ++ [.store .w .a4 .a3 (o + 4 * k)]

/-- The operation `core` on operands at any offsets: on the pointers if they
are multiples of 8 (`t0` zero), else on byte-wise copies in the own working
space, the result copied back a byte at a time to `[o]`, kept in `t1`. -/
def fn (core : Prog isa) : Prog isa :=
  .seq (.block zext) <| .seq (.block ptrs) <|
    .ite (.zero .t0) core
      (.seq (.block ([.addi .t1 .t2 0] ++ unpack .t4 SA 0 ++ unpack .t5 SB 0 ++
          [.addi .t4 .a3 SA, .addi .t5 .a3 SB, .addi .t2 .a3 SO])) <|
        .seq core (.block (pack .t1 SO 0)))

/-- `vg_p384_mul_mod_p`. -/
def mulFn : Prog isa := fn mulCore

/-- `vg_p384_add_mod_p`. -/
def addFn : Prog isa := fn (.block addCore)

/-- `vg_p384_sub_mod_p`. -/
def subFn : Prog isa := fn (.block subCore)

end VG.Impl.Weierstrass.RISCV64.P384Field
