module

public import VerifiedGarbage.Impl.Ed448.PPC64LE.ScalarBase
public import VerifiedGarbage.Impl.Ed448.PPC64LE.Scalar

/-!
# Ed448 on PPC64LE: verification's equation

`vg_ed448_verify_equation(pk = r3, signature = r4, challenge = r5,
scratch = r6) -> r3`: 1 if the public key `A` and `R` (the signature's first
57 bytes) decode, `S` (its last 57) is below `L`, and
`[4][S]B = [4]R + [4][k]A` for the 456-bit challenge `k`; 0 otherwise.

Field elements and their arithmetic are X448's on this target, as for
base-point multiplication (`ScalarBase.lean`), whose slots `Q` (its `R`),
`P`, `d`, `T` and the addition's temporaries are reused, and so is its
addition. The inputs are first copied into the working space (`PK`, `SG`,
`CH`), and `r3` then points at `OUT`, past X448's 4096 bytes, where X448's
`freeze` writes a fully reduced element.

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

The result is 1 if `BAD` is 0. The function uses only volatile registers,
the only branches are on loop counters, and every address is a pointer plus
a constant or a counter.
-/

@[expose] public section

namespace VG.Impl.Ed448.PPC64LE

open VG.PPC64LE
open VG.Impl.X448.PPC64LE (mul add sub cswap freeze one BITS R X2 Z2 Y)

/-! ## The working space -/

/-- The four entries of each of the 458 bits: the mask of each iteration. -/
def TAB : Nat := BITS
/-- `B` and the negations of `A` and `R`, with `Z = 1`, above the field area. -/
def BX : Nat := 2896
def BY : Nat := 2952
def NAX : Nat := 3008
def NAY : Nat := 3064
def NRX : Nat := 3120
def NRY : Nat := 3176
def ONE : Nat := 3232
/-- The inputs. -/
def PK : Nat := 3288
def SG : Nat := 3345
def CH : Nat := 3459
/-- The accumulated checks, and the sign bit of the point being decoded. -/
def BAD : Nat := 3520
def SIGN : Nat := 3528
/-- The output of `freeze`, at `r3`. -/
def OUT : Nat := 4096

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
  [.load .d .r9 .r6 BAD, .logic .or .r9 .r9 r, .store .d .r9 .r6 BAD]

/-- The OR of the fourteen words at `OUT` into `r10`. -/
def outOr : List Instr :=
  .li .r10 0 :: (List.range 14).flatMap fun k => [.load .w .r7 .r3 (4 * k), .logic .or .r10 .r10 .r7]

/-- `BAD |= 0` exactly when the element at `OUT` is 0. -/
def outZero : List Instr := outOr ++ orBad .r10

/-- The OR of the differences of the words at `OUT` and the bytes at `p`, into `BAD`. -/
def outSame (p : Nat) : List Instr :=
  .li .r10 0 :: (List.range 14).flatMap (fun k => [.load .w .r7 .r3 (4 * k), .load .w .r8 .r6 (p + 4 * k),
    .logic .xor .r7 .r7 .r8, .logic .or .r10 .r10 .r7]) ++ orBad .r10

/-! ## Copies -/

/-- The `n` bytes at `rs` to `o` in the working space. -/
def copyBytes (rs : Reg) (o n : Nat) : List Instr :=
  (List.range n).flatMap fun i => [.lbz .r7 rs i, .stb .r7 .r6 (o + i)]

/-- The element at `q` into `o`. -/
def copy (o q : Nat) : List Instr := .li .r11 0 :: sel o q q

/-! ## The square root's power -/

/-- `[R] = [Z2]^((p-3)/4)`, square and multiply over the bits of
`(p - 3) / 4 = 2⁴⁴⁶ - 2²²² - 1` from 445 down to 0 (`t = r12 - 1`): `R = R²`,
then `R = R · Z2` unless `t` is 222. -/
def rootStep : Prog isa :=
  .seq (.block [.subi .r12 .r12 1]) <| .seq (mul R R R) <|
  .seq (.block [.subi .r5 .r12 222]) (.ite (.zero .d .r5) (.block []) (mul R R Z2))

def root : Prog isa := .seq (.block (one ++ [.li .r12 446])) (.loop rootStep (.nonzero .d .r12))

/-! ## Decoding -/

/-- `y` from the bytes at `p` into `DY` and `X2`, its full reduction compared
with them, and the last byte's bits 0–6 checked and bit 7 into `SIGN`. -/
def decodeY (p : Nat) : List Instr :=
  (List.range 14).flatMap (fun k => [.load .w .r7 .r6 (p + 4 * k), .store .w .r7 .r6 (DY + 4 * k),
    .store .w .r7 .r6 (X2 + 4 * k)]) ++ freeze ++ outSame p ++
  [.lbz .r7 .r6 (p + 56), .li .r8 127, .logic .and .r8 .r7 .r8] ++ orBad .r8 ++
  [.lsr .d .r7 .r7 7, .stb .r7 .r6 SIGN] ++ constField DON 1

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
    [.subi .r10 .r10 1, .lsr .d .r10 .r10 63, .lbz .r7 .r6 SIGN, .logic .and .r8 .r10 .r7] ++ orBad .r8)

/-- `-x'` into `xo` and `y` into `yo`: `-x = (x - x) - x` if the low bit of
`x` (at `OUT`) is the sign, else `x`. -/
def decodeNeg (xo yo : Nat) : List Instr :=
  sub DTMP DXX DXX ++ sub DNEG DTMP DXX ++
  [.lbz .r8 .r3 0, .li .r9 1, .logic .and .r8 .r8 .r9, .lbz .r7 .r6 SIGN, .logic .xor .r8 .r8 .r7,
    .li .r11 0, .sub .r11 .r11 .r8] ++ sel xo DNEG DXX ++ sel yo DY DY

/-- The negation of the point at `p` into `xo` and `yo`. -/
def decode (p xo yo : Nat) : Prog isa :=
  .seq (.block (decodeY p)) <| .seq decodeX <| .seq decodeCheck (.block (decodeNeg xo yo))

/-! ## `S < L` -/

/-- The low 448 bits of `S` (copied to `DY`) plus `2⁴⁴⁸ - L` (into scalar
reduction's `SD`, which is `X2`) must not carry out, and its byte 56 must be
0. -/
def checkS : List Instr :=
  (List.range 14).flatMap (fun k => [.load .w .r7 .r6 (SG + 57 + 4 * k), .store .w .r7 .r6 (DY + 4 * k),
    .store .w .r7 .r6 (X2 + 4 * k)]) ++
  [.li .r8 1] ++ VG.Impl.X448.PPC64LE.pass .r6 SD (scalarSubtractSrc DY) ++ orBad .r8 ++
  [.lbz .r7 .r6 (SG + 57 + 56)] ++ orBad .r7

/-! ## The masks -/

/-- `TAB[4t + 3] = 1` and the others 0, then `TAB[8] = 1` (bit 2 of `4`). -/
def tabFill : Prog isa :=
  .seq (.block [.addi .r9 .r6 0, .li .r11 458, .li .r7 0, .li .r8 1])
    (.seq (.loop (.block [.stb .r7 .r9 TAB, .stb .r7 .r9 (TAB + 1), .stb .r7 .r9 (TAB + 2), .stb .r8 .r9 (TAB + 3),
        .addi .r9 .r9 4, .subi .r11 .r11 1]) (.nonzero .d .r11))
      (.block [.stb .r8 .r6 (TAB + 8)]))

/-- The bits of the byte at `r4` into `TAB[4 (8i + j + 2) + e]` at `r9 = 32 i`,
advancing both. -/
def tabBody (e : Nat) : List Instr :=
  [.lbz .r7 .r4 0] ++
  (List.range 8).flatMap (fun j => [.lsl .r8 .r7 (63 - j), .lsr .d .r8 .r8 63, .stb .r8 .r9 (TAB + 8 + 4 * j + e)]) ++
  [.addi .r4 .r4 1, .addi .r9 .r9 32, .subi .r11 .r11 1]

/-- The bits of the 57 bytes at `src` into the entries `e`. -/
def tabBits (src e : Nat) : Prog isa :=
  .seq (.block [.addi .r9 .r6 0, .addi .r4 .r6 src, .li .r11 57]) (.loop (.block (tabBody e)) (.nonzero .d .r11))

/-! ## The loop -/

/-- `P` and `T` from `Q`, `B`, `-A` and `-R` for the iteration `h = r12`:
`(-R or -A, by bit 0)` into `P` and `(B or Q, by bit 0)` into `T`, then `P`
from these by bit 1. -/
def vSelect : List Instr :=
  [.lsl .r4 .r12 63, .lsr .d .r4 .r4 63, .li .r11 0, .sub .r11 .r11 .r4] ++
    sel PX NRX NAX ++ sel PY NRY NAY ++ sel TX BX RX ++ sel TY BY RY ++ sel TZ ONE RZ ++
  [.lsl .r4 .r12 62, .lsr .d .r4 .r4 63, .li .r11 0, .sub .r11 .r11 .r4] ++
    sel PX PX TX ++ sel PY PY TY ++ sel PZ ONE TZ

/-- `T` swapped into `Q` under the mask of `TAB[h]`. -/
def vSwap : List Instr :=
  [.add .r4 .r6 .r12, .lbz .r4 .r4 TAB, .li .r11 0, .sub .r11 .r11 .r4] ++
    cswap RX TX ++ cswap RY TY ++ cswap RZ TZ

def vStep : Prog isa :=
  .seq (.block ([.subi .r12 .r12 1] ++ vSelect)) <| .seq addition (.block vSwap)

/-- `Q = (0 : 1 : 1)`, and the 1832 iterations. -/
def vLoop : Prog isa :=
  .seq (.block (constField RX 0 ++ constField RY 1 ++ constField RZ 1 ++ [.li .r12 1832]))
    (.loop vStep (.nonzero .d .r12))

/-! ## The function -/

/-- The inputs copied, `r3 = OUT`, `BAD = 0`, and the constants. -/
def vSetup : List Instr :=
  copyBytes .r3 PK 57 ++ copyBytes .r4 SG 114 ++ copyBytes .r5 CH 57 ++
  [.addi .r3 .r6 OUT, .li .r7 0, .store .d .r7 .r6 BAD] ++
  constField DK Spec.Ed448.d.val ++ constField BX Spec.Ed448.basePoint.X.val ++
  constField BY Spec.Ed448.basePoint.Y.val ++ constField ONE 1

/-- `X = 0` and `Y - Z = 0` checked, and the result: 1 less the top bit of
`BAD | -BAD`, which is set exactly when `BAD` is not 0. -/
def vFinish : List Instr :=
  freeze ++ outZero ++ sub TA RY RZ ++ copy X2 TA ++ freeze ++ outZero ++
  [.load .d .r9 .r6 BAD, .li .r8 0, .sub .r8 .r8 .r9, .logic .or .r9 .r9 .r8, .lsr .d .r9 .r9 63, .li .r3 1,
    .sub .r3 .r3 .r9]

def verifyEquation : Prog isa :=
  .seq (.block vSetup) <| .seq (decode SG NRX NRY) <| .seq (decode PK NAX NAY) <|
  .seq (.block checkS) <| .seq tabFill <| .seq (tabBits (SG + 57) 2) <| .seq (tabBits CH 1) <|
  .seq vLoop (.block vFinish)

end VG.Impl.Ed448.PPC64LE
