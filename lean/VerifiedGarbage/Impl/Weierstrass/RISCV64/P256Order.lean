module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P256Field
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-!
# Arithmetic modulo P-256's order, as functions, on RISC-V

`vg_p256_{mul,add,sub}_mod_n(ws, o, a, b)` (`Spec/Weierstrass/Mont.lean`)
for the group order `n = 2²⁵⁶ - 2²²⁴ + 2¹⁹² - 2¹²⁸ + n₀ + 2⁶⁴ n₁`, as the
functions modulo `p` (`Impl/Weierstrass/RISCV64/P256Field.lean`): the same
entry, operands and product, the same sums and differences, only the
modulus's words differ.

* Montgomery's reduction (`reduce`): round `i` takes the quotient word
  `q = w n' mod 2⁶⁴` (`n' = -n⁻¹ mod 2⁶⁴`) of the low word `w`, and adds
  `q n` with the low word dropped. As `w + q n₀ ≡ 0 (mod 2⁶⁴)`, the low word
  of `w + q n₀` is zero and its carry is `q ≠ 0` (`w` is zero if and only if
  `q` is), so only the high word of `q n₀` is needed (`mulhu`); `q n₁` is
  `mul` and `mulhu`; and `q (n₂ + 2⁶⁴ n₃) = q (2¹²⁸ - 2⁹⁶ + 2⁶⁴ - 1)`, which
  is `2⁶⁴ q (2⁶⁴ - 2³² + 1) - q`, is shifts and subtractions (P-256's `quot`,
  then `qk`). A round multiplies four times, the reduction sixteen.
* `csub`: `x + (2²⁵⁶ - n)` (`2²⁵⁶ - n = [c₀, c₁, 0, 2³² - 1]`), then P-256's
  `csubTail`.
* `subCore`: `n`'s words under the mask of the borrow are `n₀ ∧ m`,
  `n₁ ∧ m`, `m` and `m << 32`.

The words `n'`, `n₀`, `n₁`, `c₀` and `c₁` are built by `li64` where they are
used, from immediates. The functions are otherwise as those modulo `p`:
constant time, caller-saved registers only, and writes only to `[o]` and
their own working space.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.P256Order

open VG.RISCV64
open VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Impl.Words.RISCV64 (li64)

/-- `n`'s two low words, `-n⁻¹ mod 2⁶⁴`, and the two low words of `2²⁵⁶ - n`. -/
def N0 : BitVec 64 := 0xf3b9cac2fc632551
def N1 : BitVec 64 := 0xbce6faada7179e84
def NINV : BitVec 64 := 0xccd1c8aaee00bc4f
def C0 : BitVec 64 := 0x0c46353d039cdaaf
def C1 : BitVec 64 := 0x4319055258e8617b

/-! ## Montgomery's reduction -/

/-- The quotient word `q = w n'` of `w` in `rw i`, in place; `a5 + 2⁶⁴ a6`
the high word of `q n₀`, plus `q ≠ 0`, plus `q n₁`. -/
def qprod (i : Nat) : List Instr :=
  li64 .t0 .a0 NINV ++ [.mul (rw i) (rw i) .t0] ++
  li64 .a4 .a0 N0 ++ [.mulhu .a4 (rw i) .a4] ++
  li64 .a5 .a0 N1 ++ [.mulhu .a6 (rw i) .a5, .mul .a5 (rw i) .a5] ++
  [.li .a0 0, .sltu .a0 .a0 (rw i), .add .a4 .a4 .a0] ++
  [.add .a5 .a5 .a4, .sltu .a7 .a5 .a4, .add .a6 .a6 .a7]

/-- From `X = a6 + 2⁶⁴ a7 = q (2⁶⁴ - 2³² + 1)` (`quot i`), the words
`a4`, `a6`, `a7` of `2⁶⁴ X - q`. -/
def qk (i : Nat) : List Instr :=
  [.li .t0 0, .sub .a4 .t0 (rw i), .sltu .t0 .t0 (rw i), .sltu .a5 .a6 .t0, .sub .a6 .a6 .t0,
    .sub .a7 .a7 .a5]

/-- Round `i`: word `i + 4` of the product loaded, the quotient word, then
`rw (i + 1)`–`rw (i + 4)` plus `(w + q n) / 2⁶⁴` and the carry `a2` of the
round before, the carry out into `a2`. -/
def round (i : Nat) : List Instr :=
  [.load .d (rw (i + 4)) .a3 (ACC + 8 * (i + 4))] ++ qprod i ++
  [.add (rw (i + 1)) (rw (i + 1)) .a5, .sltu .a0 (rw (i + 1)) .a5] ++
  [.add (rw (i + 2)) (rw (i + 2)) .a6, .sltu .a7 (rw (i + 2)) .a6, .add (rw (i + 2)) (rw (i + 2)) .a0,
    .sltu .a0 (rw (i + 2)) .a0, .add .a0 .a0 .a7] ++
  quot i ++ qk i ++
  [.add (rw (i + 2)) (rw (i + 2)) .a4, .sltu .t0 (rw (i + 2)) .a4, .add .t0 .t0 .a0] ++
  [.add (rw (i + 3)) (rw (i + 3)) .t0, .sltu .a0 (rw (i + 3)) .t0] ++
  [.add (rw (i + 3)) (rw (i + 3)) .a6, .sltu .a5 (rw (i + 3)) .a6, .add .a0 .a0 .a5] ++
  [.add .a7 .a7 .a0, .add .a7 .a7 .a2, .add (rw (i + 4)) (rw (i + 4)) .a7, .sltu .a2 (rw (i + 4)) .a7]

/-- The product at `ACC` reduced, as P-256's `reduce`. -/
def reduce : List Instr :=
  (List.range 4).map (fun j => .load .d (rw j) .a3 (ACC + 8 * j)) ++ [.li .a2 0] ++
    (List.range 4).flatMap round

/-! ## The final subtraction -/

/-- `x + (2²⁵⁶ - n)` into `t6`, `a4`–`a6`, its carry into `a7`. -/
def sumN : List Instr :=
  li64 .t0 .a0 C0 ++ [.add .t6 X0 .t0, .sltu .a7 .t6 .t0] ++
  li64 .t0 .a0 C1 ++ csubWord .a4 X1 ++
  [.add .a5 X2 .a7, .sltu .a7 .a5 .a7] ++
  [.li .t0 (-1), .shift .srl .d .t0 .t0 32] ++ csubWord .a6 X3

/-- `x mod n` at `[t2]`, for `x` below `2n`. -/
def csub : List Instr := sumN ++ csubTail

/-! ## The operations -/

/-- `[t2] = [t4] [t5] R⁻¹ mod n`. -/
def mulCore : Prog isa := mulWith reduce sumN

/-- `[t2] = [t4] + [t5] mod n`. -/
def addCore : List Instr := addSum ++ csub

/-- `[t2] = [t4] - [t5] mod n`. -/
def subCore : List Instr :=
  subWith (li64 .t6 .a0 N0 ++ [.logic .and .t6 .t6 .t0]) (li64 .t6 .a0 N1 ++ [.logic .and .t6 .t6 .t0])
    [.addi .t6 .t0 0] [.shift .sll .d .t6 .t0 32]

/-- `vg_p256_mul_mod_n`. -/
def mulFn : Prog isa := fn mulCore

/-- `vg_p256_add_mod_n`. -/
def addFn : Prog isa := fn (.block addCore)

/-- `vg_p256_sub_mod_n`. -/
def subFn : Prog isa := fn (.block subCore)

end VG.Impl.Weierstrass.RISCV64.P256Order
