module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P384Field
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-!
# Arithmetic modulo P-384's order, as functions, on RISC-V

`vg_p384_{mul,add,sub}_mod_n(ws, o, a, b)` (`Proof/Weierstrass/MontContract.lean`)
for the group order `n = 2³⁸⁴ - c`, `c = c₀ + 2⁶⁴ c₁ + 2¹²⁸ c₂` below
`2¹⁹⁰`, as the functions modulo `p` (`Impl/Weierstrass/RISCV64/P384Field.lean`):
the same entry, operands and product, the same sums and differences, only
the modulus's words and the reduction's quotient differ.

* Montgomery's reduction (`reduce`): round `i` takes the quotient word
  `q = w n' mod 2⁶⁴` (`n' = -n⁻¹ = c₀⁻¹ mod 2⁶⁴`) of the low word `w`, and,
  as modulo `p`, subtracts `q c` (whose low word is `w`) and keeps `q` for
  `finish` to add `Q 2³⁸⁴`. `q c` is three `mul`/`mulhu` pairs but the low
  word of `q c₀`, which `w` is (`qc`): a round multiplies six times, the
  reduction thirty-six.
* `csub`: `x + c` (`sumNKs`), then the field's `csubTail`.
* `subCore`: `n`'s words under the mask of the borrow: `nⱼ ∧ m` for its
  three low words, then `m` three times.

The words `n'`, `c₀`–`c₂` and `n₀`–`n₂` are built by `li64` where they are
used, from immediates. The functions are otherwise as those modulo `p`:
constant time, caller-saved registers only, and writes only to `[o]` and
their own working space.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.P384Order

open VG.RISCV64
open VG.Impl.Weierstrass.RISCV64.P384Field
open VG.Impl.Words.RISCV64 (li64)

/-- `-n⁻¹ mod 2⁶⁴`, the words of `c = 2³⁸⁴ - n`, and the low words of `n`. -/
def NINV : BitVec 64 := 0x6ed46089e88fdc45
def C0 : BitVec 64 := 0x1313e695333ad68d
def C1 : BitVec 64 := 0xa7e5f24db74f5885
def C2 : BitVec 64 := 0x389cb27e0bc8d220
def N0 : BitVec 64 := 0xecec196accc52973
def N1 : BitVec 64 := 0x581a0db248b0a77a
def N2 : BitVec 64 := 0xc7634d81f4372ddf

/-! ## Montgomery's reduction -/

/-- Words 1 to 3 of `q c`, for `q` in `r`, into `a4`, `a5`, `a6`, through
`t0`, `a0` and `a7`: the high word of `q c₀`, plus `q c₁`, plus `2⁶⁴ q c₂`. -/
def qc (r : Reg) : List Instr :=
  li64 .t0 .a0 C0 ++ [.mulhu .a4 r .t0] ++
  li64 .t0 .a0 C1 ++ [.mul .a5 r .t0, .mulhu .a6 r .t0, .add .a4 .a4 .a5, .sltu .a5 .a4 .a5, .add .a6 .a6 .a5] ++
  li64 .t0 .a0 C2 ++ [.mul .a7 r .t0, .mulhu .a0 r .t0, .add .a5 .a6 .a7, .sltu .a6 .a5 .a7, .add .a6 .a6 .a0]

/-- The quotient word `q = w n'` of `w`, in place in `r`, through `t0` and `a0`. -/
def quotN (r : Reg) : List Instr := li64 .t0 .a0 NINV ++ [.mul r r .t0]

/-- The product at `ACC` reduced, as modulo `p`, by the rounds of `quotN`
and `qc`. -/
def reduce : List Instr := reduceWith quotN qc

/-! ## The final subtraction and the operations -/

/-- The words of `c = 2³⁸⁴ - n` into `t0`. -/
def sumNKs : List (List Instr) :=
  [li64 .t0 .a6 C0, li64 .t0 .a6 C1, li64 .t0 .a6 C2, [.li .t0 0]]

/-- `x mod n` at `[t2]`, for `x` below `2n`. -/
def csub : List Instr := sumWith sumNKs ++ csubTail

/-- `[t2] = [t4] [t5] R⁻¹ mod n`. -/
def mulCore : Prog isa := mulWith reduce (sumWith sumNKs)

/-- `[t2] = [t4] + [t5] mod n`. -/
def addCore : List Instr := addSum ++ csub

/-- `n`'s words under the mask `M` in `t0`: `nⱼ ∧ M` for its low three, then
`M` three times. -/
def subNKs : List (List Instr) :=
  [li64 .a6 .a0 N0 ++ [.logic .and .a6 .a6 .t0], li64 .a6 .a0 N1 ++ [.logic .and .a6 .a6 .t0],
    li64 .a6 .a0 N2 ++ [.logic .and .a6 .a6 .t0], [.addi .a6 .t0 0], [.addi .a6 .t0 0], [.addi .a6 .t0 0]]

/-- `[t2] = [t4] - [t5] mod n`. -/
def subCore : List Instr := subWith subNKs

/-- `vg_p384_mul_mod_n`. -/
def mulFn : Prog isa := fn mulCore

/-- `vg_p384_add_mod_n`. -/
def addFn : Prog isa := fn (.block addCore)

/-- `vg_p384_sub_mod_n`. -/
def subFn : Prog isa := fn (.block subCore)

end VG.Impl.Weierstrass.RISCV64.P384Order
