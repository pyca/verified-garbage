module

public import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
public import VerifiedGarbage.Impl.Ed448.RISCV64.Scalar
public import VerifiedGarbage.Impl.Ed448.PublicTable

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
  `t = u³v`, the candidate `x = t (t (uv)²)^((p-3)/4)` (`root`, X448's
  addition chain for the inversion as far as `z^(2²²³ - 1)`, then 223
  squarings), the check `v x² = u`, the check that `x = 0` comes with the
  sign 0, and the negation of the decoded point, `(-x', y)` for `x' = x`
  if its low bit is the sign and `-x` otherwise: `-x` (as `(x - x) - x`)
  if the low bit is the sign, else `x`. Its `Z` is 1 (`ONE`).
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
open VG.Impl.X448.RISCV64.R64 (mul add sub cswap chain223 sqn T6)

/-! ## The working space -/

/-- The negations of `A` and `R`, with `Z = 1`, above the field slots. -/
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

/-- `[R] = [Z2]^((p-3)/4)`, by X448's addition chain as far as
`z^(2²²³ - 1)` (in `R`, and `z^(2²²² - 1)` in `T6`), then 223 squarings and
the product with `z^(2²²² - 1)`: `(p-3)/4 = (2²²³ - 1) 2²²³ + (2²²² - 1)`. -/
def root : Prog isa := .seq (chain223 Z2) (.seq (sqn R R 223) (mul R R T6))

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

/-! ## The digits -/

/-- The bits and digits of `S` and `k`, from `a0`: entry `n < 465` is the
four bytes at `TB + 4 n`, bit `n` of `S` (lane 0) and of `k` (lane 1), and
the digits at `n` of `S` (lane 2) and of `k` (lane 3). -/
def TB : Nat := 2104

/-- The 465 entries zeroed. -/
def bitsZero : Prog isa :=
  .seq (.block [.addi .a6 .a0 0, .li .t0 465, .li .a4 0])
    (.loop (.block [.store .w .a4 .a6 (TB - OUT), .addi .a6 .a6 4, .addi .t0 .t0 (-1)]) (.nonzero .t0))

/-- The bits of the byte at `a1` into lane `e` of the entries `8 i + j` at
`a6 = OUT + 32 i`, advancing both. -/
def bitsBody (e : Nat) : List Instr :=
  [.load .b .a4 .a1 0] ++
  (List.range 8).flatMap (fun j => [.shift .sll .d .a5 .a4 (63 - j), .shift .srl .d .a5 .a5 63,
    .store .b .a5 .a6 (TB - OUT + 4 * j + e)]) ++
  [.addi .a1 .a1 1, .addi .a6 .a6 32, .addi .t0 .t0 (-1)]

/-- The bits of the 57 bytes at `src` into lane `e`. -/
def bitsOf (src e : Nat) : Prog isa :=
  .seq (.block [.addi .a6 .a0 0, .addi .a1 .a3 src, .li .t0 57]) (.loop (.block (bitsBody e)) (.nonzero .t0))

/-- The five bits at `n = (a6 - OUT) / 4` of lane `e`, `bits` into `a4`;
the digit `rawDigit false (bits + c + 16)` of the carry `c` (in `a7`) into
lane `e + 2`, and the next carry `(c + bits % 2 + 16 - digit) / 2`. -/
def recodeBody (e : Nat) : List Instr :=
  [.load .b .a4 .a6 (TB - OUT + e)] ++
  (List.range 4).flatMap (fun j => [.load .b .a5 .a6 (TB - OUT + 4 * (j + 1) + e),
    .shift .sll .d .a5 .a5 (j + 1), .logic .or .a4 .a4 .a5]) ++
  [.add .a5 .a4 .a7, .addi .a5 .a5 16, .logicImm .and .a5 .a5 31,
    .logicImm .and .t3 .a5 1, .shift .srl .d .t4 .a5 4, .shift .sll .d .t4 .t4 5, .sub .t4 .a5 .t4,
    .li .t5 0, .sub .t5 .t5 .t3, .logic .and .t4 .t4 .t5,
    .store .b .t4 .a6 (TB - OUT + e + 2),
    .logicImm .and .t3 .a4 1, .add .a7 .a7 .t3, .addi .a7 .a7 16, .sub .a7 .a7 .t4, .shift .srl .d .a7 .a7 1,
    .addi .a6 .a6 4, .addi .t0 .t0 (-1)]

/-- The 461 width-5 digits of lane `e` into lane `e + 2`, from the carry 16. -/
def recode (e : Nat) : Prog isa :=
  .seq (.block [.addi .a6 .a0 0, .li .a7 16, .li .t0 461]) (.loop (.block (recodeBody e)) (.nonzero .t0))

/-! ## The tables -/

/-- The odd multiples `[2 i + 1](-A)`, `i < 8`, projective, 168 bytes each
(`X`, `Y`, `Z`), from `a0`. -/
def KT : Nat := 3968
/-- The odd multiples `[2 i + 1]B`, `i < 8`, affine, 112 bytes each (`x`,
`y`): `PublicTable.entry i`. -/
def BT : Nat := 5312

/-- The element at `q` into `o`. -/
def copySlot (o q : Nat) : List Instr :=
  (List.range 7).flatMap fun k => [.load .d .a4 .a3 (q + 8 * k), .store .d .a4 .a3 (o + 8 * k)]

/-- The elements at `r + off + 56 j` into the slots `os[j]`. -/
def ldSlots (r : Reg) (off : Nat) (os : List Nat) : List Instr :=
  (List.range os.length).flatMap fun j => (List.range 7).flatMap fun k =>
    [.load .d .a4 r (off + 56 * j + 8 * k), .store .d .a4 .a3 (os.getD j 0 + 8 * k)]

/-- The slots `os[j]` into `r + off + 56 j`. -/
def stSlots (r : Reg) (off : Nat) (os : List Nat) : List Instr :=
  (List.range os.length).flatMap fun j => (List.range 7).flatMap fun k =>
    [.load .d .a4 .a3 (os.getD j 0 + 8 * k), .store .d .a4 r (off + 56 * j + 8 * k)]

/-- `-A` (with `Z = 1`) into `R` and the table's entry 0 (at `t2`), `R`
doubled and into `P`, and `R` back from entry 0. -/
def keyHead : Prog isa :=
  .seq (.block (copySlot RX NAX ++ copySlot RY NAY ++ copySlot RZ ONE ++ [.addi .t2 .a0 (KT - OUT)] ++
      stSlots .t2 0 [RX, RY, RZ]))
    (.seq (opsProg dblOps) (.block (copySlot PX RX ++ copySlot PY RY ++ copySlot PZ RZ ++
      ldSlots .t2 0 [RX, RY, RZ] ++ [.li .t1 7])))

/-- The next entry: `T = R + 2(-A)`, stored and into `R`. -/
def keyStep : Prog isa :=
  .seq addition (.block ([.addi .t2 .t2 168] ++ stSlots .t2 0 [TX, TY, TZ] ++
    copySlot RX TX ++ copySlot RY TY ++ copySlot RZ TZ ++ [.addi .t1 .t1 (-1)]))

def keyTable : Prog isa := .seq keyHead (.loop keyStep (.nonzero .t1))

/-- `PublicTable`'s first eight entries at `a3 + BT`, `a3` moved there and back. -/
def baseTable : List Instr :=
  [.addi .a3 .a3 2047, .addi .a3 .a3 2047, .addi .a3 .a3 (BT - 4094 : Nat)] ++
  (List.range 8).flatMap (fun i => constField (112 * i) (Impl.Ed448.PublicTable.entry i).1.val ++
    constField (112 * i + 56) (Impl.Ed448.PublicTable.entry i).2.val) ++
  [.addi .a3 .a3 (-2048), .addi .a3 .a3 (-2048), .addi .a3 .a3 (-((BT - 4096 : Nat) : Int))]

/-! ## The loop -/

/-- The digit of lane `e` at `n = t1` into `a5`. -/
def loadDigit (e : Nat) : List Instr :=
  [.shift .sll .d .a1 .t1 2, .add .a1 .a0 .a1, .load .b .a5 .a1 (TB - OUT + e)]

/-- The digit's byte in `a5` sign-extended: its sign mask (`-1` if negative)
into `a6`, and `|d| / 2`, the index of its entry, into `a5`. -/
def digitIndex : List Instr :=
  [.shift .sll .d .a5 .a5 56, .shift .sra .d .a5 .a5 56, .shift .sra .d .a6 .a5 63,
    .logic .xor .a5 .a5 .a6, .sub .a5 .a5 .a6, .shift .srl .d .a5 .a5 1]

/-- `R = R ± [|d|]B` for `S`'s digit `d ≠ 0`: the entry into `(SX, SY)`,
`SX` negated if `d < 0`, and the affine addition. -/
def addBase : Prog isa :=
  .seq (.block (loadDigit 2)) <| .ite (.nonzero .a5)
    (.seq (.block (digitIndex ++ [.shift .sll .d .t0 .a5 7, .shift .sll .d .a5 .a5 4, .sub .t0 .t0 .a5,
        .add .t0 .t0 .a0, .addi .t2 .t0 2047, .addi .t2 .t2 (BT - OUT - 2047 : Nat)] ++ ldSlots .t2 0 [SX, SY]))
      (.seq (.ite (.nonzero .a6) (.block (sub U0 SX SX ++ sub SX U0 SX)) (.block [])) (opsProg addOps)))
    (.block [])

/-- `R = R ± [|d|](-A)` for `k`'s digit `d ≠ 0`: the entry into `P`, `PX`
negated if `d < 0`, the addition, and `T` into `R`. -/
def addKey : Prog isa :=
  .seq (.block (loadDigit 3)) <| .ite (.nonzero .a5)
    (.seq (.block (digitIndex ++ [.shift .sll .d .t0 .a5 7, .shift .sll .d .a2 .a5 5, .add .t0 .t0 .a2,
        .shift .sll .d .a2 .a5 3, .add .t0 .t0 .a2, .add .t0 .t0 .a0, .addi .t2 .t0 (KT - OUT)] ++
        ldSlots .t2 0 [PX, PY, PZ]))
      (.seq (.ite (.nonzero .a6) (.block (sub TA PX PX ++ sub PX TA PX)) (.block []))
        (.seq addition (.block (copySlot RX TX ++ copySlot RY TY ++ copySlot RZ TZ)))))
    (.block [])

/-- One position `n = t1 - 1`, from the top: `R = [2]R + [S_n]B + [k_n](-A)`. -/
def jointStep : Prog isa :=
  .seq (.block [.addi .t1 .t1 (-1)]) (.seq (opsProg dblOps) (.seq addBase addKey))

/-- `R = (0 : 1 : 1)`, and the 461 positions. -/
def jointLoop : Prog isa :=
  .seq (.block (constField RX 0 ++ constField RY 1 ++ constField RZ 1 ++ [.li .t1 461]))
    (.loop jointStep (.nonzero .t1))

/-- `R = [4](R + (-R'))`, `R'` the signature's point. -/
def addNegR : Prog isa :=
  .seq (.block (copySlot SX NRX ++ copySlot SY NRY)) (.seq (opsProg addOps) (.seq (opsProg dblOps) (opsProg dblOps)))

/-! ## The function -/

/-- The working space rounded up, the inputs copied, `a0 = OUT`, `BAD = 0`,
and the constants. -/
def vSetup : List Instr :=
  align ++ copyBytes .a0 0 PK 57 ++ copyBytes .a1 0 SG 57 ++ copyBytes .a1 57 SGS 57 ++ copyBytes .a2 0 CH 57 ++
  [.addi .a0 .a3 2047, .addi .a0 .a0 1, .li .a4 0, .store .d .a4 .a3 BAD] ++
  constField DK Spec.Ed448.d.val ++ constField ONE 1

/-- `X = 0` and `Y - Z = 0` checked, and the result: 1 less the top bit of
`BAD | -BAD`, which is set exactly when `BAD` is not 0. -/
def vFinish : List Instr :=
  freeze ++ outZero ++ sub TA RY RZ ++ copy X2 TA ++ freeze ++ outZero ++
  [.load .d .a6 .a3 BAD, .li .a5 0, .sub .a5 .a5 .a6, .logic .or .a6 .a6 .a5, .shift .srl .d .a6 .a6 63, .li .a0 1,
    .sub .a0 .a0 .a6]

def verifyEquation : Prog isa :=
  .seq (.block vSetup) <| .seq (decode SG NRX NRY) <| .seq (decode PK NAX NAY) <|
  .seq (.block checkS) <| .seq bitsZero <| .seq (bitsOf SGS 0) <| .seq (bitsOf CH 1) <|
  .seq (recode 0) <| .seq (recode 1) <| .seq keyTable <| .seq (.block baseTable) <|
  .seq jointLoop <| .seq addNegR (.block vFinish)

end VG.Impl.Ed448.RISCV64
