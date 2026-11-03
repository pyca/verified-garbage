module

public import VerifiedGarbage.Impl.X25519.RISCV64.R64
public import VerifiedGarbage.Impl.Ed25519.RISCV64.MulFn

/-!
# Arithmetic modulo P-256's prime, as functions, on RISC-V

`vg_p256_{mul,add,sub}_mod_p(ws, o, a, b)` (`Proof/Weierstrass/MontContract.lean`;
`ws` in `a0`, the offsets in the low words of `a1`–`a3`), for
`p = 2²⁵⁶ - 2²²⁴ + 2¹⁹² + 2⁹⁶ - 1`, numbers of four 64-bit words:

1. the offsets are zero-extended (`zext`), and `t2`, `t4` and `t5` point to
   `[o]`, `[a]` and `[b]`; `a3` is `ws + 2048`, the base of the code of
   X25519's 64-bit products (`Impl/X25519/RISCV64/R64.lean`), which reaches
   the function's own working space (bytes 3840 to 4095 of `ws`, 1792 to
   2047 from `a3`) with short offsets;
2. if the three pointers are multiples of 8 (`aligned`: `ws` is, so their
   offsets are), the operation runs on them (`core`); else the operands are
   copied a byte at a time into the own working space (`SA`, `SB`), the
   operation runs there with its result to `SO`, and the result is copied a
   byte at a time to `[o]`, whose pointer the copies keep in `t1`;
3. the operation:
   * `mulCore`: `fused`, the product of `[t5]` and `[t4]` by columns of
     `mul` and `mulhu` in registers, with Montgomery's reduction added into
     the columns, whose quotient words need no multiplication: for
     `p ≡ -1 (mod 2⁶⁴)`, the quotient word `q` of column `i < 4` is its low
     word itself, and `q (p + 1) / 2⁶⁴ = q 2³² + q (2⁶⁴ - 2³² + 1) 2¹²⁸` is
     shifts and subtractions (`qShift`, `qMul`); columns 4 to 7 leave a
     number below `2p`, which `csub` reduces;
   * `addCore`: the sum with carries, then `csub`;
   * `subCore`: the difference with borrows, and `p` added back under the
     mask of the borrow.
   `csub`: `x + (2²⁵⁶ - p)` with carries; `x ≥ p` if and only if that or
   `x`'s top bit carries out of 256 bits, whose mask selects the sum's
   low words or `x`, stored at `[t2]`.

Every multiplication is `mul` or `mulhu`, every selection a mask, and the
only branches are on the pointers, which are public, as every address is a
pointer plus a constant. The functions use only caller-saved registers and
no stack, and write only `[o]` and their own working space.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.P256Field

open VG.RISCV64
open VG.Impl.X25519.RISCV64.R64 (product square)

/-! ## Layout, from `a3 = ws + 2048` -/

/-- The copies of the operands, and the product's eight words. -/
def MA : Nat := 1792
def MB : Nat := 1824
def ACC : Nat := 1856

/-- The byte-wise copies of the operands and the result, for offsets that
are not multiples of 8. -/
def SA : Nat := 1952
def SB : Nat := 1984
def SO : Nat := 2016

/-! ## Entry -/

/-- The offsets zero-extended: only their low words are arguments (Ed25519's
`mulZext`). -/
abbrev zext : List Instr := Ed25519.RISCV64.mulZext

/-- `t2 = ws + o`, `t4 = ws + a`, `t5 = ws + b`, `a3 = ws + 2048`, and in `t0`
the low three bits of the pointers or'ed. -/
def ptrs : List Instr :=
  [.add .t2 .a0 .a1, .add .t4 .a0 .a2, .add .t5 .a0 .a3, .addi .a3 .a0 2047, .addi .a3 .a3 1,
    .logic .or .t0 .t2 .t4, .logic .or .t0 .t0 .t5, .logicImm .and .t0 .t0 7]

/-! ## The final subtraction -/

/-- The result words of a reduction or a sum, `x₀`–`x₃`, and the top bit. -/
def X0 : Reg := .a1
def X1 : Reg := .t3
def X2 : Reg := .t4
def X3 : Reg := .t5
def XC : Reg := .a2

/-- Word `j > 0` of `x + N`, `N = 2²⁵⁶ - p`, into `d`: the constant in `t0`,
the carry in and out in `a7`, through `a0`. -/
def csubWord (d x : Reg) : List Instr :=
  [.add d x .t0, .sltu .a0 d .t0, .add d d .a7, .sltu .a7 d .a7, .add .a7 .a7 .a0]

/-- `d = x ⊕ ((x ⊕ e) ∧ m)` for the mask `m` in `t0`, stored at `[t2 + 8j]`. -/
def selWord (x e : Reg) (j : Nat) : List Instr :=
  [.logic .xor e e x, .logic .and e e .t0, .logic .xor e e x, .store .d e .t2 (8 * j)]

/-- `x + N` (`N = 2²⁵⁶ - p = [1, 2⁶⁴ - 2³², 2⁶⁴ - 1, 2³² - 2]`) into `t6`,
`a4`–`a6`, its carry into `a7`. -/
def sumP : List Instr :=
  [.addi .t6 X0 1, .sltu .a7 .t6 X0] ++
  [.li .t0 (-1), .shift .sll .d .t0 .t0 32] ++ csubWord .a4 X1 ++
  [.li .t0 (-1)] ++ csubWord .a5 X2 ++
  [.li .t0 (-1), .shift .srl .d .t0 .t0 32, .addi .t0 .t0 (-1)] ++ csubWord .a6 X3

/-- After a sum `x + (2²⁵⁶ - m)` into `t6`, `a4`–`a6` and its carry `a7`: the
carry or `c` (`x ≥ m`) as a mask, which selects the sum or `x`, stored at
`[t2]`. -/
def csubTail : List Instr :=
  [.logic .or .a7 .a7 XC, .li .t0 0, .sub .t0 .t0 .a7] ++
  selWord X0 .t6 0 ++ selWord X1 .a4 1 ++ selWord X2 .a5 2 ++ selWord X3 .a6 3

/-- `x mod p` at `[t2]`, for the number `x = x₀ + … + 2¹⁹² x₃ + 2²⁵⁶ c`
below `2p`. -/
def csub : List Instr := sumP ++ csubTail

/-! ## Montgomery's reduction of a product at `ACC`

The words and quotient of a round of the reductions of the four-word moduli
that keep their product at `ACC` (`Impl/Weierstrass/RISCV64/P256Order.lean`,
`Impl/Weierstrass/RISCV64/Gen4.lean`). -/

/-- The words of a round, rotating: round `i` reads `q = rw i` and adds into
`rw (i + 1)`–`rw (i + 4)`. -/
def RW : List Reg := [.t3, .t4, .t5, .t6, .a1]

def rw (i : Nat) : Reg := RW.getD (i % 5) .t3

/-- `q 2³² + 2¹²⁸ q (2⁶⁴ - 2³² + 1)` for `q` in `rw i`: `q 2³²` as `a4 + 2⁶⁴ a5`
(`q << 32`, `q >> 32`), `q (2⁶⁴ - 2³² + 1)` as `a6 + 2⁶⁴ a7` (`q - (q << 32)`
with its borrow, `q - (q >> 32)` less it), through `t0`. -/
def quot (i : Nat) : List Instr :=
  [.shift .sll .d .a4 (rw i) 32, .shift .srl .d .a5 (rw i) 32, .sub .a6 (rw i) .a4,
    .sltu .a7 (rw i) .a4, .sub .t0 (rw i) .a5, .sub .a7 .t0 .a7]

/-! ## The operations -/

/-- The four doublewords at `[p]` to `[a3 + o]`, through `t3`, `t6`, `a1`, `a4`. -/
def copyIn (p : Reg) (o : Nat) : List Instr :=
  [.load .d .t3 p 0, .load .d .t6 p 8, .load .d .a1 p 16, .load .d .a4 p 24,
    .store .d .t3 .a3 o, .store .d .t6 .a3 (o + 8), .store .d .a1 .a3 (o + 16),
    .store .d .a4 .a3 (o + 24)]

/-- The product of `[t4]` and `[t5]` at `ACC`: a square if the pointers are equal. -/
def prodCode : Prog isa :=
  .ite (.eq .t4 .t5) (.block (copyIn .t4 MA ++ square ACC MA))
    (.block (copyIn .t4 MA ++ copyIn .t5 MB ++ product ACC MA MB))

/-- The product, reduced by `red` and `sum ++ csubTail`. -/
def mulWith (red sum : List Instr) : Prog isa := .seq prodCode (.block (red ++ (sum ++ csubTail)))

/-! ## The product, reduced as it is computed

`fused` (`mulCore`) computes `([t5] [t4] + Q p) / 2²⁵⁶` by columns, as
`product` does, but in registers, and adds Montgomery's reduction into the
columns: the quotient word `qᵢ` is the low word of column `i < 4` (for
`p ≡ -1 (mod 2⁶⁴)`), whose `qᵢ p` cancels the word and adds `qᵢ 2³²` into
column `i + 1` (`qShift`) and `qᵢ (2⁶⁴ - 2³² + 1)` into column `i + 3`
(`qMul`), so that columns 4 to 7 are the result. Every term is two words
`x + 2⁶⁴ y`, with `y < 2⁶⁴ - 1`, added into the column's three words
(`acc3`), or, while the column's higher words are still zero, into two words
and a new third (`accF`) or one word and a new second (`acc1`). The words of
`[t4]` stay in registers; those of `[t5]` are loaded for each term. -/

/-- `x + 2⁶⁴ y = a b`. -/
def prodW (x y a b : Reg) : List Instr := [.mulhu y a b, .mul x a b]

/-- `x + 2⁶⁴ y = q 2³²`. -/
def qShift (x y q : Reg) : List Instr := [.shift .sll .d x q 32, .shift .srl .d y q 32]

/-- `x + 2⁶⁴ y = q (2⁶⁴ - 2³² + 1)`: `x = q - (q << 32)` with its borrow,
`y = q - (q >> 32)` less it; `q` is lost. -/
def qMul (x y q : Reg) : List Instr :=
  [.shift .sll .d x q 32, .sltu y q x, .sub x q x, .sub y q y, .shift .srl .d q q 32, .sub y y q]

/-- `r₀ + 2⁶⁴ r₁ + 2¹²⁸ r₂ += x + 2⁶⁴ y`. -/
def acc3 (r0 r1 r2 x y : Reg) : List Instr :=
  [.add r0 r0 x, .sltu x r0 x, .add y y x, .add r1 r1 y, .sltu y r1 y, .add r2 r2 y]

/-- `r₀ + 2⁶⁴ r₁ += x + 2⁶⁴ y`, the carry out into `y`. -/
def accF (r0 r1 x y : Reg) : List Instr :=
  [.add r0 r0 x, .sltu x r0 x, .add y y x, .add r1 r1 y, .sltu y r1 y]

/-- `r₀ += x + 2⁶⁴ y`, the high word into `y`. -/
def acc1 (r0 x y : Reg) : List Instr := [.add r0 r0 x, .sltu x r0 x, .add y y x]

/-- `a b` added by `acc3`, through `x` and `y`. -/
def pa3 (r0 r1 r2 x y a b : Reg) : List Instr := prodW x y a b ++ acc3 r0 r1 r2 x y

/-- `a b` added by `accF`. -/
def paF (r0 r1 x y a b : Reg) : List Instr := prodW x y a b ++ accF r0 r1 x y

/-- `a b` added by `acc1`. -/
def pa1 (r0 x y a b : Reg) : List Instr := prodW x y a b ++ acc1 r0 x y

/-- `q 2³²` added by `acc3`. -/
def qs3 (r0 r1 r2 x y q : Reg) : List Instr := qShift x y q ++ acc3 r0 r1 r2 x y

/-- `q (2⁶⁴ - 2³² + 1)` added by `accF`. -/
def qmF (r0 r1 x y q : Reg) : List Instr := qMul x y q ++ accF r0 r1 x y

/-- Word `i` of `[t5]` times `b`, loaded into `x`, added by `pa3`. -/
def term3 (r0 r1 r2 x y : Reg) (i : Nat) (b : Reg) : List Instr :=
  .load .d x .t5 (8 * i) :: pa3 r0 r1 r2 x y x b

/-- Columns 0 and 1: `b₀`, `b₁` into `a0`, `a4`; the column words
`a5` (`q₀`), `a6` (`q₁`), and `t0`, `t6` for column 2. -/
def col01 : List Instr :=
  [.load .d .a0 .t4 0, .load .d .a4 .t4 8, .load .d .a5 .t5 0] ++ prodW .a5 .a6 .a5 .a0 ++
  .load .d .a7 .t5 8 :: pa1 .a6 .a7 .t0 .a7 .a0 ++
  .load .d .a7 .t5 0 :: paF .a6 .t0 .a7 .t6 .a7 .a4 ++
  qs3 .a6 .t0 .t6 .a7 .a1 .a5

/-- Column 2: `b₂` into `a7`; `q₂` in `t0`, then `t6`, `a1` for column 3. -/
def col2 : List Instr :=
  .load .d .a7 .t4 16 :: .load .d .t3 .t5 16 :: paF .t0 .t6 .t3 .a1 .t3 .a0 ++
  term3 .t0 .t6 .a1 .t3 .a2 1 .a4 ++ term3 .t0 .t6 .a1 .t3 .a2 0 .a7 ++
  qs3 .t0 .t6 .a1 .t3 .a2 .a6

/-- Column 3: `q₀`'s second term, `b₃` into `a0` once `b₀` is used; `q₃` in
`t6`, then `a1`, `t3` for column 4. -/
def col3 : List Instr :=
  qmF .t6 .a1 .a2 .t3 .a5 ++
  term3 .t6 .a1 .t3 .a5 .a2 3 .a0 ++ .load .d .a0 .t4 24 ::
  term3 .t6 .a1 .t3 .a5 .a2 2 .a4 ++ term3 .t6 .a1 .t3 .a5 .a2 1 .a7 ++
  term3 .t6 .a1 .t3 .a5 .a2 0 .a0 ++ qs3 .t6 .a1 .t3 .a5 .a2 .t0

/-- Column 4: word 3 of `[t5]` kept in `a6`; the result's word 0 in `a1`,
then `t3`, `t4` for column 5. -/
def col4 : List Instr :=
  qmF .a1 .t3 .a5 .t4 .a6 ++
  .load .d .a6 .t5 24 :: pa3 .a1 .t3 .t4 .a5 .a2 .a6 .a4 ++
  term3 .a1 .t3 .t4 .a5 .a2 2 .a7 ++ term3 .a1 .t3 .t4 .a5 .a2 1 .a0 ++
  qs3 .a1 .t3 .t4 .a5 .a2 .t6

/-- Columns 5 and 6: the result's words 1 to 3 in `t3`, `t4`, `t5`, its top
bit in `a2`. -/
def col56 : List Instr :=
  .load .d .a5 .t5 16 :: qmF .t3 .t4 .a4 .t5 .t0 ++
  pa3 .t3 .t4 .t5 .a5 .a2 .a5 .a0 ++ pa3 .t3 .t4 .t5 .a5 .a2 .a6 .a7 ++
  qmF .t4 .t5 .a4 .a2 .t6 ++ pa3 .t4 .t5 .a2 .a4 .a5 .a6 .a0

/-- `X0`–`X3` and `XC`: `([t5] [t4] + Q p) / 2²⁵⁶` for some `Q < 2²⁵⁶`. -/
def fused : List Instr := col01 ++ col2 ++ col3 ++ col4 ++ col56

/-- `[t2] = [t4] [t5] R⁻¹ mod p`. -/
def mulCore : Prog isa := .block (fused ++ csub)

/-- The words of `[t4]` and `[t5]` into `a1`, `t3`, `t6`, `a4` and `a5`, `a6`,
`a7`, `t0`. -/
def loadAB : List Instr :=
  [.load .d .a1 .t4 0, .load .d .t3 .t4 8, .load .d .t6 .t4 16, .load .d .a4 .t4 24,
    .load .d .a5 .t5 0, .load .d .a6 .t5 8, .load .d .a7 .t5 16, .load .d .t0 .t5 24]

/-- Word `j > 0` of a sum into `d = x + y + c` (`c` in `a2`, in and out),
through `a5`. -/
def addWord (d x y : Reg) : List Instr :=
  [.add d x y, .sltu .a5 d y, .add d d .a2, .sltu .a2 d .a2, .add .a2 .a2 .a5]

/-- The sum of `[t4]` and `[t5]` into `X0`–`X3` and `XC`. -/
def addSum : List Instr :=
  loadAB ++ [.add .a1 .a1 .a5, .sltu .a2 .a1 .a5] ++ addWord .t3 .t3 .a6 ++ addWord .t4 .t6 .a7 ++
    addWord .t5 .a4 .t0

/-- `[t2] = [t4] + [t5] mod p`. -/
def addCore : List Instr := addSum ++ csub

/-- Word `j > 0` of a difference into `d = x - y - c` (`c` in `a2`, in and
out), through `a5`. -/
def subWord (d x y : Reg) : List Instr :=
  [.sltu .a5 x y, .sub d x y, .sltu .a0 d .a2, .sub d d .a2, .add .a2 .a5 .a0]

/-- Word `j` of `x + (p ∧ m)` for the mask `m` in `t0` (`p`'s word `j` in
`t6`), the carry in and out in `a7` (none in for `j = 0`), through `a0`,
stored at `[t2 + 8j]`. -/
def addPWord (x : Reg) (j : Nat) : List Instr :=
  (if j = 0 then [.add x x .t6, .sltu .a7 x .t6]
   else [.add x x .t6, .sltu .a0 x .t6, .add x x .a7, .sltu .a7 x .a7, .add .a7 .a7 .a0]) ++
  [.store .d x .t2 (8 * j)]

/-- The difference of `[t4]` and `[t5]` into `a1`, `t3`, `t4`, `t5`, its borrow into `a2`. -/
def subDiff : List Instr :=
  loadAB ++ [.sltu .a2 .a1 .a5, .sub .a1 .a1 .a5] ++ subWord .t3 .t3 .a6 ++ subWord .t4 .t6 .a7 ++
    subWord .t5 .a4 .t0

/-- `[t2] = [t4] - [t5] mod m`: the difference, then the borrow as a mask in
`t0`, and `m` under it added a word at a time, word `j` put into `t6` by `kⱼ`. -/
def subWith (k0 k1 k2 k3 : List Instr) : List Instr :=
  subDiff ++ [.li .t0 0, .sub .t0 .t0 .a2] ++
  k0 ++ addPWord .a1 0 ++ k1 ++ addPWord .t3 1 ++ k2 ++ addPWord .t4 2 ++ k3 ++ addPWord .t5 3

/-- `[t2] = [t4] - [t5] mod p`: `p`'s words under the mask `m` are `m`, `m >> 32`,
`0` and `(m << 32) | (m >> 63)`. -/
def subCore : List Instr :=
  subWith [.addi .t6 .t0 0] [.shift .srl .d .t6 .t0 32] [.li .t6 0]
    [.shift .sll .d .t6 .t0 32, .shift .srl .d .a4 .t0 63, .logic .or .t6 .t6 .a4]

/-! ## The functions -/

/-- The operation `core` on operands at any offsets: on the pointers if they
are multiples of 8 (`t0` zero), else on byte-wise copies in the own working
space, the result copied back a byte at a time to `[o]`, kept in `t1`. -/
def fn (core : Prog isa) : Prog isa :=
  .seq (.block zext) <| .seq (.block ptrs) <|
    .ite (.zero .t0) core
      (.seq (.block ([.addi .t1 .t2 0] ++ Ed25519.RISCV64.unpackField .t4 SA 0 ++
          Ed25519.RISCV64.unpackField .t5 SB 0 ++
          [.addi .t4 .a3 SA, .addi .t5 .a3 SB, .addi .t2 .a3 SO])) <|
        .seq core (.block (Ed25519.RISCV64.packField .t1 SO 0)))

/-- `vg_p256_mul_mod_p`. -/
def mulFn : Prog isa := fn mulCore

/-- `vg_p256_add_mod_p`. -/
def addFn : Prog isa := fn (.block addCore)

/-- `vg_p256_sub_mod_p`. -/
def subFn : Prog isa := fn (.block subCore)

end VG.Impl.Weierstrass.RISCV64.P256Field
