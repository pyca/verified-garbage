module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Spec.Secp256k1

/-!
# Arithmetic modulo secp256k1's prime on RISC-V

`vg_secp256k1_{mul,add,sub}_mod_p`, as `Gen4`'s for any four-word modulus but
for the words of `p = 2²⁵⁶ - c`, `c = 2³² + 977`:

* Montgomery's reduction (`reduce`): round `i` takes the quotient word
  `q = w m'` of the low word `w` (`m' = -p⁻¹ = c⁻¹ mod 2⁶⁴`, in `t0` for all
  rounds), and adds `q p = q 2²⁵⁶ - q c`: the low word of `q c` is `w`, so the
  low word cancels; its high word `h` (`mulhu` by `c`, in `a6`) is subtracted
  from the next word with its borrow taken through the two after, and `q`
  less the last borrow is added into word `i + 4`, with the carry of the round
  before. A round multiplies twice, against `Gen4`'s eight.
* `sum`: `x + c`, a word and then its carry.
* `subCore`: `p`'s words under the mask of the borrow: `p₀` built by `li64`
  and the mask itself for the other three.

The product, the final selection, the entry and everything else are `Gen4`'s
(P-256's).
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.Secp256k1Field

open VG.RISCV64
open VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Impl.Words.RISCV64 (li64)

/-- `c = 2²⁵⁶ - p`. -/
def c : Nat := 2 ^ 32 + 977

/-! ## Montgomery's reduction -/

/-- Round `i` (`Gen4.top` adds into the top word): word `i + 4` of the product loaded, the quotient word
`q = w m'` in place of `w = rw i`, `h = (q c) >> 64` into `a4`, subtracted from
`rw (i + 1)` with its borrow through `rw (i + 2)` and `rw (i + 3)`, then
`q` less the last borrow and the carry `a2` of the round before into
`rw (i + 4)`, the carry out of it into `a2`. -/
def round (i : Nat) : List Instr :=
  [.load .d (rw (i + 4)) .a3 (ACC + 8 * (i + 4)), .mul (rw i) (rw i) .t0, .mulhu .a4 (rw i) .a6,
   .sltu .a5 (rw (i + 1)) .a4, .sub (rw (i + 1)) (rw (i + 1)) .a4,
   .sltu .a7 (rw (i + 2)) .a5, .sub (rw (i + 2)) (rw (i + 2)) .a5,
   .sltu .a5 (rw (i + 3)) .a7, .sub (rw (i + 3)) (rw (i + 3)) .a7,
   .sub .a4 (rw i) .a5] ++ Gen4.top (rw (i + 4))

/-- The product at `ACC` reduced: its low four words loaded, the carry zero,
`m'` into `t0` and `c` into `a6`, the four rounds, leaving `rw 4`–`rw 7`
(`X0`–`X3`) and `a2` (`XC`). -/
def reduce : List Instr :=
  (List.range 4).map (fun j => .load .d (rw j) .a3 (ACC + 8 * j)) ++ [.li .a2 0] ++
    li64 .t0 .a0 (BitVec.ofNat 64 (Gen4.negInv Spec.Secp256k1.p)) ++ li64 .a6 .a0 (BitVec.ofNat 64 c) ++
    (List.range 4).flatMap round

/-! ## The final subtraction -/

/-- `x + c` into `t6`, `a4`–`a6`, its carry into `a7`, through `t0`. -/
def sum : List Instr :=
  li64 .t0 .a0 (BitVec.ofNat 64 c) ++
  [.add .t6 X0 .t0, .sltu .a7 .t6 .t0, .add .a4 X1 .a7, .sltu .a7 .a4 .a7,
   .add .a5 X2 .a7, .sltu .a7 .a5 .a7, .add .a6 X3 .a7, .sltu .a7 .a6 .a7]

/-! ## The operations -/

/-- `[t2] = [t4] [t5] R⁻¹ mod p`. -/
def mulCore : Prog isa := mulWith reduce sum

/-- `[t2] = [t4] + [t5] mod p`. -/
def addCore : List Instr := addSum ++ (sum ++ csubTail)

/-- `[t2] = [t4] - [t5] mod p`: `p₀ = 2⁶⁴ - c` under the mask, and the mask
itself for `p₁ = p₂ = p₃ = 2⁶⁴ - 1`. -/
def subCore : List Instr :=
  subWith (li64 .t6 .a0 (BitVec.ofNat 64 (2 ^ 64 - c)) ++ [.logic .and .t6 .t6 .t0])
    [.addi .t6 .t0 0] [.addi .t6 .t0 0] [.addi .t6 .t0 0]

/-- `vg_secp256k1_mul_mod_p`. -/
def mulFn : Prog isa := fn mulCore

/-- `vg_secp256k1_add_mod_p`. -/
def addFn : Prog isa := fn (.block addCore)

/-- `vg_secp256k1_sub_mod_p`. -/
def subFn : Prog isa := fn (.block subCore)

/-- `vg_secp256k1_mul_mod_p`, for aligned offsets. -/
def mulFnA : Prog isa := fnA mulCore

/-- `vg_secp256k1_add_mod_p`, for aligned offsets. -/
def addFnA : Prog isa := fnA (.block addCore)

/-- `vg_secp256k1_sub_mod_p`, for aligned offsets. -/
def subFnA : Prog isa := fnA (.block subCore)

end VG.Impl.Weierstrass.RISCV64.Secp256k1Field
