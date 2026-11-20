module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P384Field
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Impl.Words.RISCV64.Word64
public import VerifiedGarbage.Impl.Words.RISCV64.Wide

/-!
# Arithmetic modulo any odd five-word modulus, as functions, on RISC-V

`vg_<name>_{mul,add,sub}_mod_<m>(ws, o, a, b)` (`Proof/Weierstrass/MontContract.lean`)
for an odd modulus `m < 2³²⁰` known when the code is generated, as the
six-word functions (`Impl/Weierstrass/RISCV64/Gen6.lean`) are, with five
words where those have six:

1. the entry is P-384's (`P384Field.zext`, `P384Field.ptrs`): `t2`, `t4` and
   `t5` point to `[o]`, `[a]` and `[b]`, and `a3` is `ws + 2048`, which
   reaches the function's own working space (bytes 3776 to 4095 of `ws`,
   1728 to 2047 from `a3`) with short offsets; operands at pointers that are
   not multiples of 8 are copied a byte at a time into it (`SA`, `SB`) and
   the result out of it (`SO`);
2. the operation:
   * `mulCore`: the operands copied to `MA` and `MB`, their product at `ACC`
     by P-384's software-pipelined columns (`P384Field.pipe`) of the terms
     of five words (`colPairs`), whose columns 10 and 11 are empty (so
     that the product has P-384's twelve words, the top two zero); its
     square, from `MA` alone, if the two pointers are equal: the cross
     products' columns, then each of the ten words doubled with the
     squares (X25519's `dblStep`). Then Montgomery's reduction (`reduce`),
     which keeps five words of the running value in registers, `gw i` to
     `gw (i + 4)` before round `i`: round `i` takes the quotient word
     `q = w m' mod 2⁶⁴` (`m' = -m⁻¹ mod 2⁶⁴`) of the low word `w` into
     `gw i` and adds `q m` with the low word dropped (Gen6's `qword` and
     `mac`), then loads word `i + 5` of the product into `gw i` and adds
     the round's carry word and the carry of the round before into it
     (Gen4's `top`). After five rounds the number, below `2 m`, is in
     P-384's `X 0`–`X 4` with its top bit in `XC`;
   * `addCore`: the sum with carries, then `csub`;
   * `subCore`: the difference with borrows, and `m` added back under the
     mask of the borrow.
   `csub`: the words of `x + (2³²⁰ - m)` with carries stored at `[t2]`;
   `x ≥ m` if and only if that or `x`'s top bit carries out of 320 bits,
   whose mask selects, word by word, the stored sum or `x`.

For aligned offsets (`mulFnA`), the multiplication builds the reduction's
constants once rather than in each round (`mulCoreR`): the quotient
constant and `m`'s five words in `s6`–`s11`, which it keeps in its own
working space (the operands' copies, free once the product is at `ACC`) and
loads back.

Every multiplication is `mul` or `mulhu`, every selection a mask, and the
only branches are on the pointers, which are public, as every address is a
pointer plus a constant. The functions use only caller-saved registers and
no stack (but `s6`–`s11`, as they were on return), and write only `[o]` and
their own working space.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.Gen5

open VG.RISCV64
open VG.Impl.Weierstrass.RISCV64.P384Field (X XC pipe terms tm sumWord selWord adcWord sbbWord addMWord movAB
  zext ptrs)
open VG.Impl.Weierstrass.RISCV64.Gen4 (wordOf negInv top)
open VG.Impl.Words.RISCV64 (li64 mulWide)
open VG.Impl.X25519.RISCV64.R64 (dblStep)

/-! ## Layout, from `a3 = ws + 2048` -/

/-- The copies of the operands, and the product's twelve words. -/
def MA : Nat := 1728
def MB : Nat := 1768
def ACC : Nat := 1816

/-- The byte-wise copies of the operands and the result, for offsets that
are not multiples of 8. -/
def SA : Nat := 1912
def SB : Nat := 1952
def SO : Nat := 1992

/-! ## Products of five words -/

/-- The terms `(i, j)` of column `k` of a product of five words, `i`
descending: none from column 9 on. -/
def colPairs (k : Nat) : List (Nat × Nat) :=
  ((List.range 5).reverse.filter fun i => i ≤ k ∧ k - i < 5).map fun i => (i, k - i)

def sqPairs (k : Nat) : List (Nat × Nat) := (colPairs k).filter fun p => p.2 < p.1

/-- The twelve words of `[a] · [b]` at `acc`, the top two zero. -/
def product (acc a b : Nat) : List Instr := pipe acc a b (terms colPairs) fun k => (colPairs k).length

/-- The words of `[a]²` at `acc`: twelve words of the cross products, ten
of them doubled with the squares. -/
def square (acc a : Nat) : List Instr :=
  pipe acc a a (terms sqPairs) (fun k => (sqPairs k).length) ++ [.li .a5 0, .li .a4 0] ++
    (List.range 10).flatMap (dblStep acc a)

/-! ## Montgomery's reduction -/

/-- The registers of the reduction's five words, from word `i` at `gw i`:
P-384's `X 0`–`X 4`. -/
def GW : List Reg := [.t5, .t6, .t3, .t4, .a1]

/-- The register of word `i` of the reduction. -/
def gw (i : Nat) : Reg := GW.getD (i % 5) .t5

variable (m : Nat)

/-- The quotient word `q = w m'` of `w` in `gw i`, in place, and in `a4` the
high word of `q m₀` plus `q ≠ 0`, through `t0` and `a5`. -/
def qword (i : Nat) : List Instr :=
  li64 .t0 .a5 (BitVec.ofNat 64 (negInv m)) ++ [.mul (gw i) (gw i) .t0] ++
  li64 .a4 .a5 (wordOf m 0) ++ [.mulhu .a4 (gw i) .a4] ++
  [.li .a5 0, .sltu .a5 .a5 (gw i), .add .a4 .a4 .a5]

/-- `gw (i + j) += q mⱼ + c`, for `q` in `gw i` and the carry word `c` in
`a4`, in and out, through `a5`–`a7`. -/
def mac (i j : Nat) : List Instr :=
  li64 .a6 .a7 (wordOf m j) ++ mulWide .a5 .a6 (gw i) .a6 ++
  [.add .a5 .a5 .a4, .sltu .a7 .a5 .a4, .add .a6 .a6 .a7,
    .add (gw (i + j)) (gw (i + j)) .a5, .sltu .a7 (gw (i + j)) .a5, .add .a4 .a6 .a7]

/-- Round `i`: the quotient word, `q m` added into `gw (i + 1)`–`gw (i + 4)`,
then word `i + 5` of the product loaded into `gw i` and the carry word and
the carry `a2` of the round before added into it, its carries into `a2`. -/
def round (i : Nat) : List Instr :=
  qword m i ++ mac m i 1 ++ mac m i 2 ++ mac m i 3 ++ mac m i 4 ++
    [.load .d (gw i) .a3 (ACC + 8 * (i + 5))] ++ top (gw i)

/-- The product at `ACC` reduced: its low five words loaded, the carry zero,
and the five rounds. -/
def reduce : List Instr :=
  (List.range 5).map (fun j => .load .d (gw j) .a3 (ACC + 8 * j)) ++ [.li .a2 0] ++
    (List.range 5).flatMap (round m)

/-! ## The sum and the difference -/

/-- `x + N` stored at `[t2]`, its carry into `a7`, for `N` whose word `j` is put
into `t0` by `ks[j]` (P-384's `sumWith`, of five words). -/
def sumWith (ks : List (List Instr)) : List Instr :=
  .li .a7 0 :: (List.range 5).flatMap fun j => ks.getD j [] ++ sumWord j

/-- After a sum `x + (2³²⁰ - m)` stored at `[t2]` and its carry `a7`: the carry
or `XC` (`x ≥ m`) as a mask, which selects the sum or `x`. -/
def csubTail : List Instr :=
  [.logic .or .a7 .a7 XC, .li .t0 0, .sub .t0 .t0 .a7] ++ (List.range 5).flatMap selWord

/-- The words of `2³²⁰ - m` into `t0`, through `a6`. -/
def sumKs : List (List Instr) :=
  (List.range 5).map fun j => li64 .t0 .a6 (wordOf (2 ^ 320 - m) j)

/-- `m`'s words under the mask in `t0`, into `a6`, through `a0`. -/
def subKs : List (List Instr) :=
  (List.range 5).map fun j => li64 .a6 .a0 (wordOf m j) ++ [.logic .and .a6 .a6 .t0]

/-! ## The operations -/

/-- The five doublewords at `[p]` to `[a3 + o]`, through `t3`, `t6`, `a1`,
`a2`, `a4`. -/
def copyIn (p : Reg) (o : Nat) : List Instr :=
  [.load .d .t3 p 0, .load .d .t6 p 8, .load .d .a1 p 16, .load .d .a2 p 24, .load .d .a4 p 32,
    .store .d .t3 .a3 o, .store .d .t6 .a3 (o + 8), .store .d .a1 .a3 (o + 16),
    .store .d .a2 .a3 (o + 24), .store .d .a4 .a3 (o + 32)]

/-- The product of `[t4]` and `[t5]` at `ACC`: a square if the pointers are equal. -/
def prodCode : Prog isa :=
  .ite (.eq .t4 .t5) (.block (copyIn .t4 MA ++ square ACC MA))
    (.block (copyIn .t4 MA ++ copyIn .t5 MB ++ product ACC MA MB))

/-- The product, reduced by `red` and `sum ++ csubTail`. -/
def mulWith (red sum : List Instr) : Prog isa := .seq prodCode (.block (red ++ (sum ++ csubTail)))

/-- The sum of `[a0]` and `[a7]` into `X 0`–`X 4` and `XC`, through `a5`, `a6`. -/
def addSum : List Instr :=
  movAB ++ .li .a2 0 :: (List.range 5).flatMap fun j =>
    [.load .d (X j) .a0 (8 * j), .load .d .a5 .a7 (8 * j)] ++ adcWord (X j) .a5

/-- The difference of `[a0]` and `[a7]` into `X 0`–`X 4`, its borrow into `a2`. -/
def subDiff : List Instr :=
  movAB ++ .li .a2 0 :: (List.range 5).flatMap fun j =>
    [.load .d (X j) .a0 (8 * j), .load .d .a5 .a7 (8 * j)] ++ sbbWord (X j) .a5

/-- `[t2] = [t4] - [t5] mod m`: the difference, then the borrow as a mask in
`t0`, and `m` under it added a word at a time, word `j` put into `a6` by
`ks[j]`. -/
def subWith (ks : List (List Instr)) : List Instr :=
  subDiff ++ [.li .t0 0, .sub .t0 .t0 .a2, .li .a7 0] ++
    (List.range 5).flatMap fun j => ks.getD j [] ++ addMWord j

/-- `[t2] = [t4] [t5] R⁻¹ mod m`. -/
def mulCore : Prog isa := mulWith (reduce m) (sumWith (sumKs m))

/-- `[t2] = [t4] + [t5] mod m`. -/
def addCore : List Instr := addSum ++ (sumWith (sumKs m) ++ csubTail)

/-- `[t2] = [t4] - [t5] mod m`. -/
def subCore : List Instr := subWith (subKs m)

/-! ## The functions -/

/-- The element at `a` (from `a3`) as the 40 bytes at `p` plus `dst`, a word
at a time. -/
def pack (p : Reg) (a dst : Nat) : List Instr :=
  (List.range 10).flatMap fun k => [.load .w .a4 .a3 (a + 4 * k)] ++ Words.RISCV64.storeLE32 .a4 .a5 p (dst + 4 * k)

/-- The 40 bytes at `p` plus `src` as the element at `o` (from `a3`). -/
def unpack (p : Reg) (o src : Nat) : List Instr :=
  (List.range 10).flatMap fun k => Words.RISCV64.loadLE32 .a4 .a5 p (src + 4 * k) ++ [.store .w .a4 .a3 (o + 4 * k)]

/-- The operation `core` on operands at any offsets: on the pointers if they
are multiples of 8 (`t0` zero), else on byte-wise copies in the own working
space, the result copied back a byte at a time to `[o]`, kept in `t1`. -/
def fn (core : Prog isa) : Prog isa :=
  .seq (.block zext) <| .seq (.block ptrs) <|
    .ite (.zero .t0) core
      (.seq (.block ([.addi .t1 .t2 0] ++ unpack .t4 SA 0 ++ unpack .t5 SB 0 ++
          [.addi .t4 .a3 SA, .addi .t5 .a3 SB, .addi .t2 .a3 SO])) <|
        .seq core (.block (pack .t1 SO 0)))

/-- The operation `core` on operands whose offsets are zero-extended
multiples of 8, as the calls pass them: `core` on the pointers (P-256's
`ptrsA`). -/
def fnA (core : Prog isa) : Prog isa := .seq (.block P256Field.ptrsA) core

/-- The function multiplying modulo `m`. -/
def mulFn : Prog isa := fn (mulCore m)

/-- The function adding modulo `m`. -/
def addFn : Prog isa := fn (.block (addCore m))

/-- The function subtracting modulo `m`. -/
def subFn : Prog isa := fn (.block (subCore m))

/-! ## The multiplication for aligned offsets, with the modulus in registers

`mulCoreR` is `mulCore` with its reduction (`reduceR`) reading the quotient
constant from `s6` and `m`'s words from `s7`–`s11` (`MR`), which it builds
once (`constsR`) rather than in each round: it keeps `s6`–`s11` in the six
doublewords from `MA` (the operands' copies, free once the product is at
`ACC`), and loads them back after the rounds. -/

/-- The register of `m`'s word `j < 5`. -/
def MR (j : Nat) : Reg := [.s7, .s8, .s9, .s10, .s11].getD j .s7

/-- The registers of the constants: `s6`, then `MR 0`–`MR 4`. -/
def KR : List Reg := [.s6, .s7, .s8, .s9, .s10, .s11]

/-- `s6`–`s11` to `[a3 + MA]`. -/
def saveM : List Instr := (List.range 6).flatMap fun j => [.store .d (KR.getD j .s6) .a3 (MA + 8 * j)]

/-- `s6`–`s11` from `[a3 + MA]`. -/
def restoreM : List Instr := (List.range 6).flatMap fun j => [.load .d (KR.getD j .s6) .a3 (MA + 8 * j)]

/-- The quotient constant to `s6`, `m`'s words to `s7`–`s11`. -/
def constsR : List Instr :=
  li64 .s6 .a5 (BitVec.ofNat 64 (negInv m)) ++ (List.range 5).flatMap fun j => li64 (MR j) .a5 (wordOf m j)

/-- `qword` with the constants in registers. -/
def qwordR (i : Nat) : List Instr :=
  [.mul (gw i) (gw i) .s6, .mulhu .a4 (gw i) (MR 0), .li .a5 0, .sltu .a5 .a5 (gw i), .add .a4 .a4 .a5]

/-- `mac` with `m`'s word `j` in `MR j`. -/
def macR (i j : Nat) : List Instr :=
  mulWide .a5 .a6 (gw i) (MR j) ++
  [.add .a5 .a5 .a4, .sltu .a7 .a5 .a4, .add .a6 .a6 .a7,
    .add (gw (i + j)) (gw (i + j)) .a5, .sltu .a7 (gw (i + j)) .a5, .add .a4 .a6 .a7]

/-- `round` with the constants in registers. -/
def roundR (i : Nat) : List Instr :=
  qwordR i ++ macR i 1 ++ macR i 2 ++ macR i 3 ++ macR i 4 ++
    [.load .d (gw i) .a3 (ACC + 8 * (i + 5))] ++ top (gw i)

/-- `reduce` with the constants in registers: `s6`–`s11` kept, the
constants, the rounds, and `s6`–`s11` back. -/
def reduceR : List Instr :=
  saveM ++ (constsR m ++ ((List.range 5).map (fun j => .load .d (gw j) .a3 (ACC + 8 * j)) ++ [.li .a2 0] ++
    (List.range 5).flatMap roundR ++ restoreM))

/-- `[t2] = [t4] [t5] R⁻¹ mod m`, with the constants in registers. -/
def mulCoreR : Prog isa := mulWith (reduceR m) (sumWith (sumKs m))

/-- The function multiplying modulo `m`, for aligned offsets. -/
def mulFnA : Prog isa := fnA (mulCoreR m)

/-- The function adding modulo `m`, for aligned offsets. -/
def addFnA : Prog isa := fnA (.block (addCore m))

/-- The function subtracting modulo `m`, for aligned offsets. -/
def subFnA : Prog isa := fnA (.block (subCore m))

end VG.Impl.Weierstrass.RISCV64.Gen5
