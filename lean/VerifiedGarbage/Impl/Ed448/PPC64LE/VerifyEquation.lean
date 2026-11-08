module

public import VerifiedGarbage.Impl.Ed448.PPC64LE.ScalarBase
public import VerifiedGarbage.Impl.Ed448.PPC64LE.Scalar
public import VerifiedGarbage.Impl.Ed448.PublicTable

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
* The digits: the bits of `S` and `k` a byte each (`bitsOf`), and from them
  the 464 width-5 digits of each (`recode`, `WnafWide.digitAt false`), each
  odd or 0 and in `(-16, 16)`, as RISC-V computes them
  (`Impl/Ed448/RISCV64/VerifyEquation.lean`): at position `n`, the five
  bits there and the carry give the digit and the next carry, without
  branches. Entry `n` of `TB` holds bit `n` of `S` and of `k` and their
  digits at `n`.
* The tables: `[2i + 1](-A)` for `i < 8`, projective, from one doubling and
  seven additions (`keyTable`), and `[2i + 1]B`, affine, the first eight
  entries of `PublicTable` (`baseTable`), above `OUT`.
* `Q = [S]B + [k](-A)`, from the top position down (`jointLoop`): `Q`
  doubled, then for each nonzero digit `d` the entry `|d| / 2` of its
  table, negated if `d < 0`, added (`addBase` affine, `addKey`
  projective). The point operations are functions the loop calls
  (`vg_ed448_r32_double`, `vg_ed448_r32_add_affine`, of `ScalarBase.lean`,
  and `vg_ed448_r32_add`, RFC 8032's addition), since a branch reaches only
  32 KiB; the position is in the nonvolatile `r14`, which no field
  operation or call writes, and whose value is kept at `VR14S`, as the
  return address is at `VLRS`, and both are loaded back at the end.
* `[4](Q + (-R))` (`addNegR`) is the neutral point exactly when the
  equation holds: `X = 0` and `Y - Z = 0`, fully reduced.

The result is 1 if `BAD` is 0. The function writes only volatile
registers, `r14` and the link register, the last two loaded back before it
returns. Its only branches are on loop counters and, in the joint loop, on
the digits of `S` and `k`, and its addresses are pointers plus constants,
counters or the digits' entries: the time depends on the inputs, which are
public.
-/

@[expose] public section

namespace VG.Impl.Ed448.PPC64LE

open VG.PPC64LE
open VG.Impl.X448.PPC64LE (mul add sub cswap freeze one BITS R X2 Z2 Y)

/-! ## The working space -/

/-- The negations of `A` and `R`, with `Z = 1`, above the field area. -/
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
/-- The return address and the caller's `r14`, while the function runs. -/
def VLRS : Nat := 3536
def VR14S : Nat := 3544
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

/-! ## The digits -/

/-- The bits and digits of `S` and `k`: entry `n < 468` is the four bytes at
`TB + 4 n`, bit `n` of `S` (lane 0) and of `k` (lane 1), and the digits at
`n` of `S` (lane 2) and of `k` (lane 3). -/
def TB : Nat := BITS

/-- The 468 entries zeroed. -/
def bitsZero : Prog isa :=
  .seq (.block [.addi .r9 .r6 0, .li .r11 468, .li .r7 0])
    (.loop (.block [.stb .r7 .r9 TB, .stb .r7 .r9 (TB + 1), .stb .r7 .r9 (TB + 2), .stb .r7 .r9 (TB + 3),
      .addi .r9 .r9 4, .subi .r11 .r11 1]) (.nonzero .d .r11))

/-- The bits of the byte at `r4` into lane `e` of the entries `8 i + j` at
`r9 = b + 32 i`, advancing both. -/
def bitsBody (e : Nat) : List Instr :=
  [.lbz .r7 .r4 0] ++
  (List.range 8).flatMap (fun j => [.lsl .r8 .r7 (63 - j), .lsr .d .r8 .r8 63, .stb .r8 .r9 (TB + 4 * j + e)]) ++
  [.addi .r4 .r4 1, .addi .r9 .r9 32, .subi .r11 .r11 1]

/-- The bits of the 57 bytes at `src` into lane `e`. -/
def bitsOf (src e : Nat) : Prog isa :=
  .seq (.block [.addi .r9 .r6 0, .addi .r4 .r6 src, .li .r11 57]) (.loop (.block (bitsBody e)) (.nonzero .d .r11))

/-- The five bits at `n` (`r9 = b + 4 n`) of lane `e`, `bits` into `r7`;
the digit `rawDigit false (bits + c + 16)` of the carry `c` (in `r10`) into
lane `e + 2`, and the next carry `(c + bits % 2 + 16 - digit) / 2`. -/
def recodeBody (e : Nat) : List Instr :=
  [.lbz .r7 .r9 (TB + e)] ++
  (List.range 4).flatMap (fun j => [.lbz .r8 .r9 (TB + 4 * (j + 1) + e), .lsl .r8 .r8 (j + 1),
    .logic .or .r7 .r7 .r8]) ++
  [.add .r8 .r7 .r10, .addi .r8 .r8 16, .li .r4 31, .logic .and .r8 .r8 .r4,
    .li .r4 1, .logic .and .r5 .r8 .r4, .lsr .d .r12 .r8 4, .lsl .r12 .r12 5, .sub .r12 .r8 .r12,
    .li .r0 0, .sub .r0 .r0 .r5, .logic .and .r12 .r12 .r0,
    .stb .r12 .r9 (TB + e + 2),
    .logic .and .r5 .r7 .r4, .add .r10 .r10 .r5, .addi .r10 .r10 16, .sub .r10 .r10 .r12, .lsr .d .r10 .r10 1,
    .addi .r9 .r9 4, .subi .r11 .r11 1]

/-- The 464 width-5 digits of lane `e` into lane `e + 2`, from the carry 16
(`WnafWide.digitAt false`). -/
def recode (e : Nat) : Prog isa :=
  .seq (.block [.addi .r9 .r6 0, .li .r10 16, .li .r11 464]) (.loop (.block (recodeBody e)) (.nonzero .d .r11))

/-! ## The tables -/

/-- The odd multiples `[2 i + 1](-A)`, `i < 8`, projective, 168 bytes each
(`X`, `Y`, `Z`), past `OUT`'s element. -/
def KT : Nat := 4160
/-- The odd multiples `[2 i + 1]B`, `i < 8`, affine, 112 bytes each (`x`,
`y`): `PublicTable.entry i`. -/
def BT : Nat := 5504

/-- The seven doublewords at `rs + so` to `rd + d`, through `r7`. -/
def cp7 (rs : Reg) (so : Nat) (rd : Reg) (d : Nat) : List Instr :=
  (List.range 7).flatMap fun k => [.load .d .r7 rs (so + 8 * k), .store .d .r7 rd (d + 8 * k)]

/-- The element at `q` into `o`. -/
def copySlot (o q : Nat) : List Instr := cp7 .r6 q .r6 o

/-- The elements at `r + off + 56 j` into the slots `os[j]`. -/
def ldSlots (r : Reg) (off : Nat) (os : List Nat) : List Instr :=
  (List.range os.length).flatMap fun j => cp7 r (off + 56 * j) .r6 (os.getD j 0)

/-- The slots `os[j]` into `r + off + 56 j`. -/
def stSlots (r : Reg) (off : Nat) (os : List Nat) : List Instr :=
  (List.range os.length).flatMap fun j => cp7 .r6 (os.getD j 0) r (off + 56 * j)

/-- RFC 8032's addition `T = R + P` (`addition`'s operations), a function. -/
def projOps : List COp :=
  [.mul TA RZ PZ, .mul TY TA TA, .mul TC RX PX, .mul TD RY PY, .mul TZ DK TC, .mul TZ TZ TD,
    .sub TF TY TZ, .add TG TY TZ, .add TH RX RY, .add TX PX PY, .mul TH TH TX, .mul TX TA TF,
    .sub TH TH TC, .sub TH TH TD, .mul TX TX TH, .mul TY TA TG, .sub TH TD TC, .mul TY TY TH, .mul TZ TF TG]

def callProj : Prog isa := .call "vg_ed448_r32_add" (opsProg projOps)

/-- `-A` (with `Z = 1`) into `R` and the table's entry 0, `R` doubled and
into `P`, `R` back from entry 0, and the counter of the other entries. -/
def keyHead : Prog isa :=
  .seq (.block (copySlot RX NAX ++ copySlot RY NAY ++ copySlot RZ ONE ++ stSlots .r6 KT [RX, RY, RZ]))
    (.seq callDbl (.block (copySlot PX RX ++ copySlot PY RY ++ copySlot PZ RZ ++
      ldSlots .r6 KT [RX, RY, RZ] ++ [.li .r14 7])))

/-- `r12 = b + 168 i` for the entry `i = 8 - r14`. -/
def keyPtr : List Instr :=
  [.li .r4 8, .sub .r4 .r4 .r14, .lsl .r12 .r4 7, .lsl .r5 .r4 5, .add .r12 .r12 .r5, .lsl .r5 .r4 3,
    .add .r12 .r12 .r5, .add .r12 .r12 .r6]

/-- The entry `8 - r14`: `T = R + 2(-A)`, stored and into `R`. -/
def keyStep : Prog isa :=
  .seq callProj (.block (keyPtr ++ stSlots .r12 KT [TX, TY, TZ] ++ copySlot RX TX ++ copySlot RY TY ++
    copySlot RZ TZ ++ [.subi .r14 .r14 1]))

def keyTable : Prog isa := .seq keyHead (.loop keyStep (.nonzero .d .r14))

/-- `PublicTable`'s first eight entries at `BT`. -/
def baseTable : List Instr :=
  (List.range 8).flatMap fun i => constField (BT + 112 * i) (Impl.Ed448.PublicTable.entry i).1.val ++
    constField (BT + 112 * i + 56) (Impl.Ed448.PublicTable.entry i).2.val

/-! ## The loop -/

/-- The digit of lane `e` at `n = r14` into `r10`. -/
def loadDigit (e : Nat) : List Instr := [.lsl .r9 .r14 2, .add .r9 .r6 .r9, .lbz .r10 .r9 (TB + e)]

/-- The digit's byte `d` in `r10`: its sign mask (all ones if `d ≥ 128`, a
negative digit) into `r12`, and `|d| / 2`, the index of its entry, into `r10`
(`|d| = ((d ⊕ m) - m) mod 256` for the mask `m`). -/
def digitIndex : List Instr :=
  [.lsr .d .r8 .r10 7, .li .r12 0, .sub .r12 .r12 .r8, .logic .xor .r10 .r10 .r12, .sub .r10 .r10 .r12,
    .li .r8 255, .logic .and .r10 .r10 .r8, .lsr .d .r10 .r10 1]

/-- `R = R ± [|d|]B` for `S`'s digit `d ≠ 0`: the entry into `(SX, SY)`,
`SX` negated if `d < 0`, and the affine addition. -/
def baseBody : Prog isa :=
  .seq (.block (digitIndex ++ [.lsl .r9 .r10 7, .lsl .r8 .r10 4, .sub .r9 .r9 .r8, .add .r9 .r9 .r6] ++
      ldSlots .r9 BT [SX, SY]))
    (.seq (.ite (.nonzero .d .r12) (.block (sub U0 SX SX ++ sub SX U0 SX)) (.block [])) callAdd)

def addBase : Prog isa := .seq (.block (loadDigit 2)) (.ite (.nonzero .d .r10) baseBody (.block []))

/-- `R = R ± [|d|](-A)` for `k`'s digit `d ≠ 0`: the entry into `P`, `PX`
negated if `d < 0`, the addition, and `T` into `R`. -/
def keyBody : Prog isa :=
  .seq (.block (digitIndex ++ [.lsl .r9 .r10 7, .lsl .r8 .r10 5, .add .r9 .r9 .r8, .lsl .r8 .r10 3,
      .add .r9 .r9 .r8, .add .r9 .r9 .r6] ++ ldSlots .r9 KT [PX, PY, PZ]))
    (.seq (.ite (.nonzero .d .r12) (.block (sub TA PX PX ++ sub PX TA PX)) (.block []))
      (.seq callProj (.block (copySlot RX TX ++ copySlot RY TY ++ copySlot RZ TZ))))

def addKey : Prog isa := .seq (.block (loadDigit 3)) (.ite (.nonzero .d .r10) keyBody (.block []))

/-- One position `n = r14 - 1`, from the top: `R = [2]R + [S_n]B + [k_n](-A)`. -/
def jointStep : Prog isa :=
  .seq (.block [.subi .r14 .r14 1]) (.seq callDbl (.seq addBase addKey))

/-- `R = (0 : 1 : 1)`, and the 464 positions. -/
def jointLoop : Prog isa :=
  .seq (.block (constField RX 0 ++ constField RY 1 ++ constField RZ 1 ++ [.li .r14 464]))
    (.loop jointStep (.nonzero .d .r14))

/-- `R = [4](R + (-R'))`, `R'` the signature's point. -/
def addNegR : Prog isa :=
  .seq (.block (copySlot SX NRX ++ copySlot SY NRY)) (.seq callAdd (.seq callDbl callDbl))

/-! ## The function -/

/-- The return address and `r14` kept, the inputs copied, `r3 = OUT`,
`BAD = 0`, and the constants. -/
def vSetup : List Instr :=
  [.mflr .r7, .store .d .r7 .r6 VLRS, .store .d .r14 .r6 VR14S] ++
  copyBytes .r3 PK 57 ++ copyBytes .r4 SG 114 ++ copyBytes .r5 CH 57 ++
  [.addi .r3 .r6 OUT, .li .r7 0, .store .d .r7 .r6 BAD] ++
  constField DK Spec.Ed448.d.val ++ constField ONE 1

/-- The return address and `r14` loaded back. -/
def vRestore : List Instr := [.load .d .r7 .r6 VLRS, .mtlr .r7, .load .d .r14 .r6 VR14S]

/-- `X = 0` and `Y - Z = 0` checked, and the result: 1 less the top bit of
`BAD | -BAD`, which is set exactly when `BAD` is not 0. -/
def vFinish : List Instr :=
  freeze ++ outZero ++ sub TA RY RZ ++ copy X2 TA ++ freeze ++ outZero ++
  [.load .d .r9 .r6 BAD, .li .r8 0, .sub .r8 .r8 .r9, .logic .or .r9 .r9 .r8, .lsr .d .r9 .r9 63, .li .r3 1,
    .sub .r3 .r3 .r9]

/-- Everything before the joint loop, whose branches are only on loop counters. -/
def vPrefix : Prog isa :=
  .seq (.block vSetup) <| .seq (decode SG NRX NRY) <| .seq (decode PK NAX NAY) <|
  .seq (.block checkS) <| .seq bitsZero <| .seq (bitsOf (SG + 57) 0) <| .seq (bitsOf CH 1) <|
  .seq (recode 0) <| .seq (recode 1) <| .seq keyTable (.block baseTable)

def verifyEquation : Prog isa :=
  .seq vPrefix <| .seq jointLoop <| .seq addNegR (.block (vRestore ++ vFinish))

end VG.Impl.Ed448.PPC64LE
