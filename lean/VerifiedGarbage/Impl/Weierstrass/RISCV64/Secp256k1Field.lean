module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Rows
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
(P-256's), but the multiplication for aligned offsets (`mulFnA`) is by rows, in
registers (`Impl/Weierstrass/RISCV64/Rows.lean`), with a reduction of its own.
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

/-! ## The multiplication for aligned offsets, by rows in registers

`Rows`' product or square, then `redTail`, Montgomery's reduction in one pass
for a modulus `2²⁵⁶ - c`: the quotient `q` of all four rounds is a chain of
`q' c + C = w + 2⁶⁴ C'` (`qStep`: a word `q'` in `w`'s place and a carry `C`),
so that `q c` is the product's low half plus `2²⁵⁶ h`, with `h` the last carry.
The product plus `q p` is then `2²⁵⁶` times its high half `+ q - h`. The sum `S`
of the high half and `q` (`sumStep`) gives both `S - h` and, its reduction,
`S + (c - h) - 2²⁵⁶`, chosen by a mask. -/

/-- The registers, and where in the own working space those kept and the product are. -/
def lay : Rows.Lay where
  k := 4
  VL := [.t0, .a7, .a5, .a6]
  AL := [.a0, .a1, .a2, .a4]
  LO := [.t6, .t1, .s7]
  HI := [.s8]
  KR := [.t1, .s7, .s8]
  sv := 1792
  pp := 1856

/-- A word of the quotient in place of `w`, with the carry `t3` in and out, for `m'` in `t5` and `c` in `s8`. -/
def qStep (w : Reg) : List Instr :=
  [.sltu .t6 w .t3, .sub w w .t3, .mul w w .t5, .mulhu .t3 w .s8, .add .t3 .t3 .t6]

/-- `v + 2⁶⁴ t4 := v + a + t4`. -/
def sumStep (v a : Reg) : List Instr :=
  [.add v v a, .sltu .t6 v a, .add v v .t4, .sltu .t4 v .t4, .add .t4 .t4 .t6]

/-- The word `a`, if the mask `t4` is all ones, or `v`, into `[t2 + 8 j]`. -/
def selStep (j : Nat) (a v : Reg) : List Instr :=
  [.logic .xor a a v, .logic .and a a .t4, .logic .xor a a v, .store .d a .t2 (8 * j)]

/-- The quotient in `a0`–`a2`, `a4` and `h` in `t3`. -/
def quots : List Instr :=
  [.mul .a0 .a0 .t5, .mulhu .t3 .a0 .s8] ++ (qStep .a1 ++ (qStep .a2 ++ qStep .a4))

/-- The high half plus the quotient, its carry in `t4`. -/
def sums : List Instr :=
  [.add .t0 .t0 .a0, .sltu .t4 .t0 .a0] ++ (sumStep .a7 .a1 ++ (sumStep .a5 .a2 ++ sumStep .a6 .a4))

/-- `S + (c - h)` in `a0`–`a2`, `a4`, its carry in `t6`, and `S - h` in place of `S`. -/
def cands : List Instr :=
  [.sub .s8 .s8 .t3] ++ ([.add .a0 .t0 .s8, .sltu .t6 .a0 .s8] ++ ([.add .a1 .a7 .t6, .sltu .t6 .a1 .t6] ++
    ([.add .a2 .a5 .t6, .sltu .t6 .a2 .t6] ++ ([.add .a4 .a6 .t6, .sltu .t6 .a4 .t6] ++
    ([.sltu .t5 .t0 .t3, .sub .t0 .t0 .t3] ++ ([.sltu .t3 .a7 .t5, .sub .a7 .a7 .t5] ++
    ([.sltu .t5 .a5 .t3, .sub .a5 .a5 .t3] ++ ([.sub .a6 .a6 .t5] : List Instr))))))))

/-- The mask, and the selection. -/
def sels : List Instr :=
  [.logic .or .t4 .t4 .t6, .li .t6 0, .sub .t4 .t6 .t4] ++
    (selStep 0 .a0 .t0 ++ (selStep 1 .a1 .a7 ++ (selStep 2 .a2 .a5 ++ selStep 3 .a4 .a6)))

/-- The product's words. -/
def loads : List Instr :=
  [.load .d .a0 .a3 1856, .load .d .a1 .a3 1864, .load .d .a2 .a3 1872, .load .d .a4 .a3 1880,
    .load .d .t0 .a3 1888, .load .d .a7 .a3 1896, .load .d .a5 .a3 1904, .load .d .a6 .a3 1912]

/-- The product reduced, into `[t2]`. -/
def redTail : List Instr :=
  loads ++ (li64 .t5 .t6 (BitVec.ofNat 64 (Gen4.negInv Spec.Secp256k1.p)) ++ (li64 .s8 .t6 (BitVec.ofNat 64 c) ++
    (quots ++ (sums ++ (cands ++ sels)))))

/-- The order of the code, found by timing orders on T-Head's C910. -/
def order : Rows.Order where
  mul := [
    0, 2, 0, 0, 0, 1, 1, 2, 4, 2, 1, 0, 0, 0, 0, 0, 1, 5, 0, 0, 4, 0, 0, 0, 1, 13, 6, 0, 18, 0, 0, 17, 0, 21, 9, 0,
    14, 0, 0, 6, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 4, 4, 16, 0, 0, 15, 0, 0, 1, 12, 1, 0, 0, 0, 12, 1, 12, 1, 0, 0,
    0, 0, 0, 11, 6, 0, 1, 0, 0, 0, 0, 5, 5, 1, 16, 0, 0, 3, 0, 0, 1, 0, 10, 0, 0, 13, 1, 19, 0, 0, 1, 4, 0, 15, 0, 0,
    6, 2, 0, 4, 9, 0, 0, 0, 0, 0, 0, 0, 2]
  sqr := [
    0, 1, 0, 3, 2, 0, 2, 37, 1, 1, 1, 0, 0, 7, 1, 0, 0, 5, 2, 2, 0, 5, 0, 0, 10, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0,
    2, 1, 0, 0, 7, 2, 0, 0, 0, 0, 0, 2, 2, 2, 2, 8, 2, 1, 0, 5, 0, 0, 2, 0, 10, 1, 0, 0, 0, 4, 5, 5, 0, 2, 3, 3, 0,
    7, 2, 0, 1, 4, 0, 0, 1, 1, 1, 0, 6, 0, 6, 0, 5, 5, 0, 0, 0, 0, 1, 0, 0, 5, 0, 0, 3, 3, 0, 0, 1, 0, 8, 6, 0, 6, 0,
    0, 2, 3, 0, 0, 1, 7, 7, 1, 1, 1, 1, 1, 2, 2, 0, 1, 1, 0, 0, 2]
  tail := [
    0, 7, 7, 3, 7, 7, 6, 7, 6, 11, 1, 4, 4, 5, 4, 4, 1, 0, 2, 0, 1, 0, 15, 0, 0, 13, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0,
    7, 0, 0, 0, 0, 0, 11, 0, 18, 0, 9, 0, 0, 2, 0, 0, 0, 0, 9, 0, 0, 0, 6, 0, 12, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
    3, 0, 2, 0, 0, 2, 0, 4]

/-- `vg_secp256k1_mul_mod_p`, for aligned offsets. -/
def mulFnA : Prog isa := fnA (Rows.fastWith lay redTail order)

/-- `vg_secp256k1_add_mod_p`, for aligned offsets. -/
def addFnA : Prog isa := fnA (.block addCore)

/-- `vg_secp256k1_sub_mod_p`, for aligned offsets. -/
def subFnA : Prog isa := fnA (.block subCore)

end VG.Impl.Weierstrass.RISCV64.Secp256k1Field
