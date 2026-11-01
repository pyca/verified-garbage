module

public import VerifiedGarbage.Impl.X25519.RISCV64.R64
public import VerifiedGarbage.Impl.Ed25519.RISCV64.MulFn

/-!
# Arithmetic modulo P-256's prime, as functions, on RISC-V

`vg_p256_{mul,add,sub}_mod_p(ws, o, a, b)` (`Spec/Weierstrass/Mont.lean`;
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
   * `mulCore`: the operands copied (doublewords) to `MA` and `MB`, their
     eight-word product at `ACC` by X25519's columns of `mul` and `mulhu`
     (its square, from `MA` alone, if the two pointers are equal: six cross
     products rather than twelve), then Montgomery's reduction (`reduce`),
     whose quotient words need no multiplication: for `p ≡ -1 (mod 2⁶⁴)`,
     the quotient word of a round is the low word `q` itself, and
     `q (p + 1) / 2⁶⁴ = q 2³² + q (2⁶⁴ - 2³² + 1) 2¹²⁸` is shifts and
     subtractions (`quot`); the four rounds leave a number below `2p`,
     which `csub` reduces;
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

/-- `x mod p` at `[t2]`, for the number `x = x₀ + … + 2¹⁹² x₃ + 2²⁵⁶ c`
below `2p`: `x + N` (`N = [1, 2⁶⁴ - 2³², 2⁶⁴ - 1, 2³² - 2]`) into `t6`,
`a4`–`a6`, its carry or `c` (`x ≥ p`) as a mask, which selects it. -/
def csub : List Instr :=
  [.addi .t6 X0 1, .sltu .a7 .t6 X0] ++
  [.li .t0 (-1), .shift .sll .d .t0 .t0 32] ++ csubWord .a4 X1 ++
  [.li .t0 (-1)] ++ csubWord .a5 X2 ++
  [.li .t0 (-1), .shift .srl .d .t0 .t0 32, .addi .t0 .t0 (-1)] ++ csubWord .a6 X3 ++
  [.logic .or .a7 .a7 XC, .li .t0 0, .sub .t0 .t0 .a7] ++
  selWord X0 .t6 0 ++ selWord X1 .a4 1 ++ selWord X2 .a5 2 ++ selWord X3 .a6 3

/-! ## Montgomery's reduction -/

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

/-- Round `i`: word `i + 4` of the product loaded, then `rw (i + 1)`–`rw (i + 4)`
plus `quot i` and the carry `a2` of the round before into word `i + 4`, the
carry out of it into `a2`. -/
def round (i : Nat) : List Instr :=
  [.load .d (rw (i + 4)) .a3 (ACC + 8 * (i + 4))] ++ quot i ++
  [.add (rw (i + 1)) (rw (i + 1)) .a4, .sltu .t0 (rw (i + 1)) .a4,
   .add .a5 .a5 .t0, .add (rw (i + 2)) (rw (i + 2)) .a5, .sltu .t0 (rw (i + 2)) .a5,
   .add (rw (i + 3)) (rw (i + 3)) .a6, .sltu .a4 (rw (i + 3)) .a6, .add (rw (i + 3)) (rw (i + 3)) .t0,
   .sltu .t0 (rw (i + 3)) .t0, .add .t0 .t0 .a4,
   .add .a7 .a7 .t0, .add .a7 .a7 .a2, .add (rw (i + 4)) (rw (i + 4)) .a7, .sltu .a2 (rw (i + 4)) .a7]

/-- The product at `ACC` reduced: its low four words loaded, the carry zero,
the four rounds, leaving `rw 4`–`rw 7` (`X0`–`X3`) and `a2` (`XC`). -/
def reduce : List Instr :=
  (List.range 4).map (fun j => .load .d (rw j) .a3 (ACC + 8 * j)) ++ [.li .a2 0] ++
    (List.range 4).flatMap round

/-! ## The operations -/

/-- The four doublewords at `[p]` to `[a3 + o]`, through `t3`, `t6`, `a1`, `a4`. -/
def copyIn (p : Reg) (o : Nat) : List Instr :=
  [.load .d .t3 p 0, .load .d .t6 p 8, .load .d .a1 p 16, .load .d .a4 p 24,
    .store .d .t3 .a3 o, .store .d .t6 .a3 (o + 8), .store .d .a1 .a3 (o + 16),
    .store .d .a4 .a3 (o + 24)]

/-- `[t2] = [t4] [t5] R⁻¹ mod p`: a square if the pointers are equal. -/
def mulCore : Prog isa :=
  .seq (.ite (.eq .t4 .t5) (.block (copyIn .t4 MA ++ square ACC MA))
    (.block (copyIn .t4 MA ++ copyIn .t5 MB ++ product ACC MA MB)))
    (.block (reduce ++ csub))

/-- The words of `[t4]` and `[t5]` into `a1`, `t3`, `t6`, `a4` and `a5`, `a6`,
`a7`, `t0`. -/
def loadAB : List Instr :=
  [.load .d .a1 .t4 0, .load .d .t3 .t4 8, .load .d .t6 .t4 16, .load .d .a4 .t4 24,
    .load .d .a5 .t5 0, .load .d .a6 .t5 8, .load .d .a7 .t5 16, .load .d .t0 .t5 24]

/-- Word `j > 0` of a sum into `d = x + y + c` (`c` in `a2`, in and out),
through `a5`. -/
def addWord (d x y : Reg) : List Instr :=
  [.add d x y, .sltu .a5 d y, .add d d .a2, .sltu .a2 d .a2, .add .a2 .a2 .a5]

/-- `[t2] = [t4] + [t5] mod p`. -/
def addCore : List Instr :=
  loadAB ++ [.add .a1 .a1 .a5, .sltu .a2 .a1 .a5] ++ addWord .t3 .t3 .a6 ++ addWord .t4 .t6 .a7 ++
    addWord .t5 .a4 .t0 ++ csub

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

/-- `[t2] = [t4] - [t5] mod p`: the difference, and `p` under the mask of the
borrow (`p`'s words `m`, `m >> 32`, `0`, `(m << 32) | (m >> 63)`) added. -/
def subCore : List Instr :=
  loadAB ++ [.sltu .a2 .a1 .a5, .sub .a1 .a1 .a5] ++ subWord .t3 .t3 .a6 ++ subWord .t4 .t6 .a7 ++
    subWord .t5 .a4 .t0 ++
  [.li .t0 0, .sub .t0 .t0 .a2] ++
  ([.addi .t6 .t0 0] : List Instr) ++ addPWord .a1 0 ++
  [.shift .srl .d .t6 .t0 32] ++ addPWord .t3 1 ++
  [.li .t6 0] ++ addPWord .t4 2 ++
  [.shift .sll .d .t6 .t0 32, .shift .srl .d .a4 .t0 63, .logic .or .t6 .t6 .a4] ++ addPWord .t5 3

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
