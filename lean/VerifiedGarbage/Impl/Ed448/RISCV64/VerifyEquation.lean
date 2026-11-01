module

public import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
public import VerifiedGarbage.Impl.Ed448.RISCV64.Scalar

/-!
# Ed448 on RISC-V: verification's equation

`vg_ed448_verify_equation(pk = a0, signature = a1, challenge = a2,
scratch = a3) -> a0`: 1 if the public key `A` and `R` (the signature's first
57 bytes) decode, `S` (its last 57) is below `L`, and
`[4][S]B = [4]R + [4][k]A` for the 456-bit challenge `k`; 0 otherwise.

The PPC64LE code (`Impl/Ed448/PPC64LE/VerifyEquation.lean`), register for
register as X448's port is, with the working space rounded up to a multiple
of 8 (`align`) and laid out for RISC-V's 12-bit offsets:

* Field elements and their arithmetic are X448's on this target, as for
  base-point multiplication (`ScalarBase.lean`), whose slots `Q` (its `R`),
  `P`, `d`, `T` and the addition's temporaries are reused, and so is its
  addition. `B`, the negations of `A` and `R`, `1`, the inputs (`PK`, `SG`
  for `R`, `SGS` for `S` and `CH`, each copied a byte at a time and starting
  at a multiple of 4, for the word loads), the checks `BAD` and the sign
  `SIGN` are above X448's slots and below 2048, so that every slot is an
  offset from `a3`.
* `a0` then points at `OUT`, at 2048, past the 2048 bytes X448 addresses
  from `a3`, where X448's `freeze` writes a fully reduced element.
* The table of masks `TAB` (1832 bytes) follows `OUT`, and its entries are
  addressed from `a0` (`TAB - OUT` plus a counter).

Everything is computed whatever the inputs, and the checks are accumulated
in the doubleword `BAD`, which stays 0 exactly when every one passes: each
check ORs into it a word that is 0 if and only if it passes.

* Decoding a point (RFC 8032 §5.2.3) from the 57 bytes at `p`: `y` from the
  first 56, which must equal their full reduction (so `y < p`), with bits
  0–6 of the last byte 0 and bit 7 the sign; `u = y² - 1`, `v = d y² - 1`,
  `t = u³v`, the candidate `x = t (t (uv)²)^((p-3)/4)` (`root`, square and
  multiply over the bits of `(p-3)/4`), the check `v x² = u`, the check that
  `x = 0` comes with the sign 0, and the negation of the decoded point,
  `(-x', y)` for `x' = x` if its low bit is the sign and `-x` otherwise:
  `-x` (as `(x - x) - x`) if the low bit is the sign, else `x`. Its `Z` is 1
  (`ONE`).
* `S < L`: its byte 56 is 0 and its low 448 bits plus `2^448 - L` (scalar
  reduction's subtraction) do not carry out of 448 bits.
* `Q = [4S]B + [4k](-A) + [4](-R)`, from the top bit down, four iterations
  of the same code per bit `t < 458` of `4S` and `4k`: `T = Q + P` (the
  addition of `ScalarBase.lean`), swapped into `Q` with the mask of the byte
  `TAB[h]` for the iteration `h = 4t + i`. `P` is `Q` for `i = 3` (a
  doubling, `TAB[h] = 1`), `B` for `i = 2` (`TAB[h]` bit `t` of `4S`), `-A`
  for `i = 1` (bit `t` of `4k`) and `-R` for `i = 0` (bit `t` of `4`),
  selected by masks of the two bits of `i`.
* The equation holds exactly when `Q` is the neutral point: `X = 0` and
  `Y - Z = 0`, fully reduced.

The result is 1 if `BAD` is 0. The function uses only caller-saved
registers and no stack, the only branches are on loop counters, and every
address is a pointer plus a constant or a counter.
-/

@[expose] public section

namespace VG.Impl.Ed448.RISCV64

open VG.RISCV64
open VG.Impl.X448.RISCV64 (freeze one align R X2 Z2 Y)
open VG.Impl.X448.RISCV64.R64 (mul add sub cswap)

/-! ## The working space -/

/-- `B` and the negations of `A` and `R`, with `Z = 1`, above the field slots. -/
def BX : Nat := 1064
def BY : Nat := 1120
def NAX : Nat := 1176
def NAY : Nat := 1232
def NRX : Nat := 1288
def NRY : Nat := 1344
def ONE : Nat := 1400
/-- The inputs: the public key, the signature's `R` and `S`, and the challenge. -/
def PK : Nat := 1456
def SG : Nat := 1516
def SGS : Nat := 1576
def CH : Nat := 1636
/-- The accumulated checks, and the sign bit of the point being decoded. -/
def BAD : Nat := 1696
def SIGN : Nat := 1704
/-- The output of `freeze`, at `a0`. -/
def OUT : Nat := 2048
/-- The four entries of each of the 458 bits: the mask of each iteration,
addressed from `a0`. -/
def TAB : Nat := 2104

/-- The slots decoding uses. -/
def DY : Nat := 168
def DON : Nat := 224
def DYY : Nat := 280
def DU : Nat := 392
def DV : Nat := 448
def DT : Nat := 504
def DW : Nat := 560
def DTMP : Nat := 616
def DXX : Nat := 672
def DNEG : Nat := 728

/-! ## Checks -/

/-- `BAD |= r`. -/
def orBad (r : Reg) : List Instr :=
  [.load .d .a6 .a3 BAD, .logic .or .a6 .a6 r, .store .d .a6 .a3 BAD]

/-- The OR of the fourteen words at `OUT` into `a7`. -/
def outOr : List Instr :=
  .li .a7 0 :: (List.range 14).flatMap fun k => [.load .w .a4 .a0 (4 * k), .logic .or .a7 .a7 .a4]

/-- `BAD |= 0` exactly when the element at `OUT` is 0. -/
def outZero : List Instr := outOr ++ orBad .a7

/-- The OR of the differences of the words at `OUT` and the bytes at `p`, into `BAD`. -/
def outSame (p : Nat) : List Instr :=
  .li .a7 0 :: (List.range 14).flatMap (fun k => [.load .w .a4 .a0 (4 * k), .load .w .a5 .a3 (p + 4 * k),
    .logic .xor .a4 .a4 .a5, .logic .or .a7 .a7 .a4]) ++ orBad .a7

/-! ## Copies -/

/-- The `n` bytes at `rs + so` to `o` in the working space. -/
def copyBytes (rs : Reg) (so o n : Nat) : List Instr :=
  (List.range n).flatMap fun i => [.load .b .a4 rs (so + i), .store .b .a4 .a3 (o + i)]

/-- The element at `q` into `o`. -/
def copy (o q : Nat) : List Instr := .li .t0 0 :: sel o q q

/-! ## The square root's power -/

/-- `[R] = [Z2]^((p-3)/4)`, square and multiply over the bits of
`(p - 3) / 4 = 2⁴⁴⁶ - 2²²² - 1` from 445 down to 0 (`t = t1 - 1`): `R = R²`,
then `R = R · Z2` unless `t` is 222. -/
def rootStep : Prog isa :=
  .seq (.block [.addi .t1 .t1 (-1)]) <| .seq (mul R R R) <|
  .seq (.block [.addi .a2 .t1 (-222)]) (.ite (.zero .a2) (.block []) (mul R R Z2))

def root : Prog isa := .seq (.block (one ++ [.li .t1 446])) (.loop rootStep (.nonzero .t1))

/-! ## Decoding -/

/-- `y` from the bytes at `p` into `DY` and `X2`, its full reduction compared
with them, and the last byte's bits 0–6 checked and bit 7 into `SIGN`. -/
def decodeY (p : Nat) : List Instr :=
  (List.range 14).flatMap (fun k => [.load .w .a4 .a3 (p + 4 * k), .store .w .a4 .a3 (DY + 4 * k),
    .store .w .a4 .a3 (X2 + 4 * k)]) ++ freeze ++ outSame p ++
  [.load .b .a4 .a3 (p + 56), .li .a5 127, .logic .and .a5 .a4 .a5] ++ orBad .a5 ++
  [.shift .srl .d .a4 .a4 7, .store .b .a4 .a3 SIGN] ++ constField DON 1

/-- `u`, `v`, `t = u³v` and `t (uv)²` (into `Z2`), its power into `R`, and
`x = t R`. -/
def decodeX : Prog isa :=
  .seq (mul DYY DY DY) <| .seq (.block (sub DU DYY DON)) <| .seq (mul DV DK DYY) <|
  .seq (.block (sub DV DV DON)) <| .seq (mul DT DU DU) <| .seq (mul DT DT DU) <|
  .seq (mul DT DT DV) <| .seq (mul DW DU DV) <| .seq (mul DW DW DW) <| .seq (mul Z2 DT DW) <|
  .seq root (mul DXX DT R)

/-- `v x² - u` fully reduced and checked to be 0, and `x` fully reduced into
`OUT`, checked not to be 0 with the sign 1. -/
def decodeCheck : Prog isa :=
  .seq (mul DTMP DXX DXX) <| .seq (mul DTMP DV DTMP) <|
  .block (sub X2 DTMP DU ++ freeze ++ outZero ++ copy X2 DXX ++ freeze ++ outOr ++
    [.addi .a7 .a7 (-1), .shift .srl .d .a7 .a7 63, .load .b .a4 .a3 SIGN, .logic .and .a5 .a7 .a4] ++ orBad .a5)

/-- `-x'` into `xo` and `y` into `yo`: `-x = (x - x) - x` if the low bit of
`x` (at `OUT`) is the sign, else `x`. -/
def decodeNeg (xo yo : Nat) : List Instr :=
  sub DTMP DXX DXX ++ sub DNEG DTMP DXX ++
  [.load .b .a5 .a0 0, .li .a6 1, .logic .and .a5 .a5 .a6, .load .b .a4 .a3 SIGN, .logic .xor .a5 .a5 .a4,
    .li .t0 0, .sub .t0 .t0 .a5] ++ sel xo DNEG DXX ++ sel yo DY DY

/-- The negation of the point at `p` into `xo` and `yo`. -/
def decode (p xo yo : Nat) : Prog isa :=
  .seq (.block (decodeY p)) <| .seq decodeX <| .seq decodeCheck (.block (decodeNeg xo yo))

/-! ## `S < L` -/

/-- The low 448 bits of `S` (copied to `DY`) plus `2⁴⁴⁸ - L` (into scalar
reduction's `SD`, which is `X2`) must not carry out, and its byte 56 must be
0. -/
def checkS : List Instr :=
  (List.range 14).flatMap (fun k => [.load .w .a4 .a3 (SGS + 4 * k), .store .w .a4 .a3 (DY + 4 * k),
    .store .w .a4 .a3 (X2 + 4 * k)]) ++
  [.li .a5 1] ++ VG.Impl.X448.RISCV64.pass .a3 SD (scalarSubtractSrc DY) ++ orBad .a5 ++
  [.load .b .a4 .a3 (SGS + 56)] ++ orBad .a4

/-! ## The masks -/

/-- `TAB[4t + 3] = 1` and the others 0, then `TAB[8] = 1` (bit 2 of `4`). -/
def tabFill : Prog isa :=
  .seq (.block [.addi .a6 .a0 0, .li .t0 458, .li .a4 0, .li .a5 1])
    (.seq (.loop (.block [.store .b .a4 .a6 (TAB - OUT), .store .b .a4 .a6 (TAB - OUT + 1),
        .store .b .a4 .a6 (TAB - OUT + 2), .store .b .a5 .a6 (TAB - OUT + 3),
        .addi .a6 .a6 4, .addi .t0 .t0 (-1)]) (.nonzero .t0))
      (.block [.store .b .a5 .a0 (TAB - OUT + 8)]))

/-- The bits of the byte at `a1` into `TAB[4 (8i + j + 2) + e]` at
`a6 = OUT + 32 i`, advancing both. -/
def tabBody (e : Nat) : List Instr :=
  [.load .b .a4 .a1 0] ++
  (List.range 8).flatMap (fun j => [.shift .sll .d .a5 .a4 (63 - j), .shift .srl .d .a5 .a5 63,
    .store .b .a5 .a6 (TAB - OUT + 8 + 4 * j + e)]) ++
  [.addi .a1 .a1 1, .addi .a6 .a6 32, .addi .t0 .t0 (-1)]

/-- The bits of the 57 bytes at `src` into the entries `e`. -/
def tabBits (src e : Nat) : Prog isa :=
  .seq (.block [.addi .a6 .a0 0, .addi .a1 .a3 src, .li .t0 57]) (.loop (.block (tabBody e)) (.nonzero .t0))

/-! ## The loop -/

/-- `P` and `T` from `Q`, `B`, `-A` and `-R` for the iteration `h = t1`:
`(-R or -A, by bit 0)` into `P` and `(B or Q, by bit 0)` into `T`, then `P`
from these by bit 1. -/
def vSelect : List Instr :=
  [.shift .sll .d .a1 .t1 63, .shift .srl .d .a1 .a1 63, .li .t0 0, .sub .t0 .t0 .a1] ++
    sel PX NRX NAX ++ sel PY NRY NAY ++ sel TX BX RX ++ sel TY BY RY ++ sel TZ ONE RZ ++
  [.shift .sll .d .a1 .t1 62, .shift .srl .d .a1 .a1 63, .li .t0 0, .sub .t0 .t0 .a1] ++
    sel PX PX TX ++ sel PY PY TY ++ sel PZ ONE TZ

/-- `T` swapped into `Q` under the mask of `TAB[h]`. -/
def vSwap : List Instr :=
  [.add .a1 .a0 .t1, .load .b .a1 .a1 (TAB - OUT), .li .t0 0, .sub .t0 .t0 .a1] ++
    cswap RX TX ++ cswap RY TY ++ cswap RZ TZ

def vStep : Prog isa :=
  .seq (.block ([.addi .t1 .t1 (-1)] ++ vSelect)) <| .seq addition (.block vSwap)

/-- `Q = (0 : 1 : 1)`, and the 1832 iterations. -/
def vLoop : Prog isa :=
  .seq (.block (constField RX 0 ++ constField RY 1 ++ constField RZ 1 ++ [.li .t1 1832]))
    (.loop vStep (.nonzero .t1))

/-! ## The function -/

/-- The working space rounded up, the inputs copied, `a0 = OUT`, `BAD = 0`,
and the constants. -/
def vSetup : List Instr :=
  align ++ copyBytes .a0 0 PK 57 ++ copyBytes .a1 0 SG 57 ++ copyBytes .a1 57 SGS 57 ++ copyBytes .a2 0 CH 57 ++
  [.addi .a0 .a3 2047, .addi .a0 .a0 1, .li .a4 0, .store .d .a4 .a3 BAD] ++
  constField DK Spec.Ed448.d.val ++ constField BX Spec.Ed448.basePoint.X.val ++
  constField BY Spec.Ed448.basePoint.Y.val ++ constField ONE 1

/-- `X = 0` and `Y - Z = 0` checked, and the result: 1 less the top bit of
`BAD | -BAD`, which is set exactly when `BAD` is not 0. -/
def vFinish : List Instr :=
  freeze ++ outZero ++ sub TA RY RZ ++ copy X2 TA ++ freeze ++ outZero ++
  [.load .d .a6 .a3 BAD, .li .a5 0, .sub .a5 .a5 .a6, .logic .or .a6 .a6 .a5, .shift .srl .d .a6 .a6 63, .li .a0 1,
    .sub .a0 .a0 .a6]

def verifyEquation : Prog isa :=
  .seq (.block vSetup) <| .seq (decode SG NRX NRY) <| .seq (decode PK NAX NAY) <|
  .seq (.block checkS) <| .seq tabFill <| .seq (tabBits SGS 2) <| .seq (tabBits CH 1) <|
  .seq vLoop (.block vFinish)

end VG.Impl.Ed448.RISCV64
