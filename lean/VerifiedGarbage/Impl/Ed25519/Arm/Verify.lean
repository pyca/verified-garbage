module

public import VerifiedGarbage.Impl.Ed25519.Arm.PointDecode
public import VerifiedGarbage.Impl.Ed25519.Arm.PointEqual
public import VerifiedGarbage.Impl.Ed25519.Arm.PointTableIO
public import VerifiedGarbage.Impl.Ed25519.Arm.ScalarABI
public import VerifiedGarbage.Impl.Ed25519.Arm.Comb

/-! Strict Ed25519 verification. The challenge is 64 bytes whose last 32 are zero (the caller
reduces it modulo `L`), so `A` is multiplied by its first 256 bits only. -/

@[expose] public section

namespace VG.Impl.Ed25519.Arm
open VG.Arm

def loadHeader (d : Nat) : List Instr := scratchAddr d ++ [.ldr .r12 .r12 0]
def verifyScalar : List Instr :=
  loadHeader 8164 ++ [.dp .add .r12 .r12 (.imm 32)] ++
    unpackField SR 0 ++ scalarCompare ++ [.cmp .r5 (.imm 0)]

/-- `[S]B` by the comb (`combMultiply`), into the table at 8032. -/
def verifyLhs (umaal : Bool) : Prog isa :=
  .seq (.block (loadHeader 8164 ++ [.dp .add .r12 .r12 (.imm 32)]))
    (.seq (combMultiply umaal) (.block (pointTableWrite 8032)))

def verifyCombine (umaal : Bool) : Prog isa :=
  .seq copyPointToQ (.seq (.block (pointTableRead 7904))
    (.seq (Point16.addCall umaal) (.seq copyPointToQ (.block (pointTableRead 8032)))))

/-! ## `[k]A` with a sliding window on `k`, which is public

`k`'s 256 bits are first recoded, from the lowest, into 256 digits, each zero or odd and below
16, a byte each from byte `DIG` of the working space (`recode`), that sum to `k` weighted by
the powers of two: a set bit that no window covers opens a window of four bits there, whose
digit is those bits' value, and the other three digits of the window are zero. A table at
byte `TBA` holds the odd multiples `[1]A, [3]A, …, [15]A` (`oddTable`), packed as the
verification's other points are. The sum (slots 0–3) starts at the entry of the top digit that
is not zero (`topDigit`, `slideStart`), and for each digit below it the sum is doubled and the
digit's entry is added where the digit is not zero (`slideStep`). The doubling is of the sum's
`X : Y : Z` (`vg_ed25519_r16_point_double`, seven products): its `T`, one more product
(`doubleTOps`), is computed only where an addition reads it, before a digit's entry is added,
and after the last digit, for the addition of `R`. The digits are the challenge's, which
verification may leak, so the branches and the table's addresses are on public data.

The recoding reads one bit a step (`recBit`), a byte of `k` at a time (`recByte`): `r9` counts
the bits read, `r10` holds the byte in hand, shifted right once a bit, `r8` the weight of the
next bit in the window in hand (zero with none: 2, 4, 8 and then none again), `r7` that
window's digit so far and `r6` the address of its byte, less `DIG`. With no window, the bit is
the digit, and opens a window if it is set; with one, the digit is zero and the bit, at its
weight, is added to the window's digit, which is stored again: the digits stored are those of
the bits read so far, and nothing is left to do after the last. -/

/-- The digits' bytes in the working space: 256 from here. -/
def DIG : Nat := 2304

/-- The table of `[1]A, [3]A, …, [15]A` in the working space: 128 bytes an entry. -/
def TBA : Nat := 4096

/-- The address of the byte of `k` (its pointer at word 52) that holds bit `r9` into `r3`. -/
def recAddr : List Instr :=
  [.ldr .r3 .r0 52, .mov .r2 (.shifted .r9 .lsr 3), .dp .add .r3 .r3 (.reg .r2)]

/-- The byte of `k` that holds bit `r9` into `r10`. -/
def recLoad : List Instr := recAddr ++ [.ldrb .r10 .r3 0]

/-- The address of digit `r9`, less `DIG`, into `r3`, the bit into `r1`, and Z set with no
window in hand. -/
def recHead : List Instr :=
  [.dp .add .r3 .r0 (.reg .r9), .dp .and .r1 .r10 (.imm 1), .cmp .r8 (.imm 0)]

/-- No window in hand: the bit is the digit, and a window's first. -/
def recOpen : List Instr :=
  [.mov .r7 (.reg .r1), .mov .r8 (.shifted .r1 .lsl 1), .mov .r6 (.reg .r3), .strb .r7 .r6 DIG]

/-- A window in hand: the digit is zero, and the bit is added to the window's digit at the
weight `r8`, which doubles, and is none after 8. -/
def recGrow : List Instr :=
  [.mov .r2 (.imm 0), .strb .r2 .r3 DIG, .dp .sub .r2 .r2 (.reg .r1), .dp .and .r2 .r2 (.reg .r8),
    .dp .add .r7 .r7 (.reg .r2), .strb .r7 .r6 DIG, .mov .r8 (.shifted .r8 .lsl 1),
    .dp .and .r8 .r8 (.imm 15)]

/-- The next bit. -/
def recNext : List Instr := [.mov .r10 (.shifted .r10 .lsr 1), .dp .add .r9 .r9 (.imm 1)]

/-- One bit, the low one of `r10`. -/
def recBit : Prog isa :=
  .seq (.block recHead) (.seq (.ite .eq (.block recOpen) (.block recGrow)) (.block recNext))

/-- `c`, `n` times, then `k`. -/
def repeatThen : Nat → Prog isa → Prog isa → Prog isa
  | 0, _, k => k
  | n + 1, c, k => .seq c (repeatThen n c k)

/-- A byte of `k`: its eight bits from the lowest. Z is set after bit 255. -/
def recByte : Prog isa :=
  .seq (.block recLoad) (repeatThen 8 recBit (.block [.cmp .r9 (.imm 256)]))

/-- No bit read, no window, and a window's address that is in the digits. -/
def recInit : List Instr :=
  [.mov .r9 (.imm 0), .mov .r8 (.imm 0), .mov .r7 (.imm 0), .mov .r6 (.reg .r0)]

/-- `k`'s digits to the bytes from `DIG`, for `k`'s pointer at word 52. -/
def recode : Prog isa := .seq (.block recInit) (.loop recByte .ne)

/-- `r12` = the address of entry `r11` of the table. -/
def entryAddr : List Instr :=
  [.movw .r12 (BitVec.ofNat 16 TBA), .dp .add .r12 .r12 (.shifted .r11 .lsl 7), .dp .add .r12 .r0 (.reg .r12)]

/-- `d` in slot 16, `A` (slots 0–3) to entry 0, `[2]A` with its `T` in slots 4–7, `A` in slots
0–3 again, and the next entry's index. -/
def oddTableInit (umaal : Bool) : Prog isa :=
  .seq (fieldCode false [.const 16 Spec.Ed25519.d]) <| .seq (.block (pointTableWrite TBA)) <|
  .seq (Point16.doubleCall umaal) <| .seq (fieldCode umaal doubleTOps) <|
  .seq copyPointToQ (.block (pointTableRead TBA ++ [.mov .r11 (.imm 1)]))

/-- Entry `r11` = entry `r11 - 1` (in slots 0–3) + `[2]A` (in slots 4–7). Z is set after
entry 7. -/
def oddTableStep (umaal : Bool) : Prog isa :=
  .seq (Point16.addCall umaal)
    (.block (entryAddr ++ pointToTable ++ [.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.imm 8)]))

/-- Entries `m < 8` of the table at `TBA` are `[2m + 1]A`, for `A` in slots 0–3. -/
def oddTable (umaal : Bool) : Prog isa := .seq (oddTableInit umaal) (.loop (oddTableStep umaal) .ne)

/-- The digit below `r11` into `r10`, Z set if it is zero. -/
def digitLoad : List Instr := [.dp .add .r3 .r0 (.reg .r11), .ldrb .r10 .r3 DIG, .cmp .r10 (.imm 0)]

/-- The position `r11` moved down, the sum's `X : Y : Z` doubled, and that position's digit
loaded. -/
def slideHead (umaal : Bool) : Prog isa :=
  .seq (.block [.dp .sub .r11 .r11 (.imm 1)]) (.seq (Point16.doubleCall umaal) (.block digitLoad))

/-- `r12` = the address of the entry of the odd digit `r10`, entry `(r10 - 1) / 2`: 64 bytes a
unit of the digit, from `TBA - 64`. -/
def digitAddr : List Instr :=
  [.movw .r12 (BitVec.ofNat 16 (TBA - 64)), .dp .add .r12 .r12 (.shifted .r10 .lsl 6),
    .dp .add .r12 .r0 (.reg .r12)]

/-- The entry of the digit `r10` added to the sum: the sum to slots 4–7, the entry to slots
0–3, and their sum. -/
def addEntry (umaal : Bool) : Prog isa :=
  .seq copyPointToQ (.seq (.block (digitAddr ++ pointFromTable)) (Point16.addCall umaal))

/-- After the doubling, with Z set if the digit is zero: for a digit that is not zero, the
sum's `T` and the digit's entry added; for one that is, the sum's `T` only after digit 0. -/
def slideTail (umaal : Bool) : Prog isa :=
  .ite .ne (.seq (fieldCode umaal doubleTOps) (addEntry umaal))
    (.seq (.block [.cmp .r11 (.imm 0)]) (.ite .eq (fieldCode umaal doubleTOps) (.block [])))

/-- One digit: the sum doubled, and the digit's entry added unless the digit is zero. Z is set
after digit 0. -/
def slideStep (umaal : Bool) : Prog isa :=
  .seq (slideHead umaal) (.seq (slideTail umaal) (.block [.cmp .r11 (.imm 0)]))

/-- One position of the search for the top digit: the position `r11` moved down and its digit
loaded. Z is clear while the digit is zero and a position is left. -/
def topStep : Prog isa :=
  .seq (.block ([.dp .sub .r11 .r11 (.imm 1)] ++ digitLoad))
    (.ite .eq (.block [.cmp .r11 (.imm 0)]) (.block [.cmp .r10 (.reg .r10)]))

/-- `r11` = the highest position whose digit is not zero (0 if every digit is zero), and `r10` =
its digit. -/
def topDigit : Prog isa := .seq (.block [.mov .r11 (.imm 256)]) (.loop topStep .ne)

/-- The sum's start: the entry of the top digit `r10`, or the identity if it is zero. -/
def slideStart : Prog isa :=
  .seq (.block [.cmp .r10 (.imm 0)])
    (.ite .ne (.block (digitAddr ++ pointFromTable)) (constPoint Spec.Ed25519.identity))

/-- The digits below the top one, at `r11`, if any. -/
def slideRest (umaal : Bool) : Prog isa :=
  .seq (.block [.cmp .r11 (.imm 0)]) (.ite .ne (.loop (slideStep umaal) .ne) (.block []))

/-- `[k]A` into slots 0–3, for `A` in slots 0–3 and the 32 bytes of `k` at `r12`: `k`'s pointer
saved, the table, `k`'s digits, and the sum over them from the top one. -/
def publicMul (umaal : Bool) : Prog isa :=
  .seq (.block [.str .r12 .r0 52]) <| .seq (oddTable umaal) <| .seq recode <| .seq topDigit <|
  .seq slideStart (slideRest umaal)

def verifyRhs (umaal : Bool) : Prog isa :=
  .seq (.block (pointTableRead 7776 ++ loadHeader 8168))
    (.seq (publicMul umaal) (.seq (verifyCombine umaal) (pointEqual umaal)))

def verifyEquationPoints (umaal : Bool) : Prog isa := .seq (verifyLhs umaal) (verifyRhs umaal)
/-! ## Decoding `A` and `R` -/

/-- The working space's words of the decodings' loop: the encoding's pointer, the table
entry's offset, and the AND of the decodings' results. -/
def DPTR : Nat := 32
def DTAB : Nat := 36
def DOK : Nat := 40

/-- `A` (`pk`, from its header at 8160) first, into the table at 7776, then `R` at 7904. -/
def decodeStart : List Instr :=
  loadHeader 8160 ++ [.str .r12 .r0 DPTR, .movw .r3 7776, .str .r3 .r0 DTAB, .mov .r3 (.imm 1),
    .str .r3 .r0 DOK]

/-- The decoding's result ANDed into `DOK`, the point to the table at `[DTAB]`, then `R`'s
pointer (its header at 8164) and the next entry; `Z` set after `R`'s. -/
def decodeNext : List Instr :=
  [.ldr .r3 .r0 DOK, .dp .and .r3 .r3 (.reg .r9), .str .r3 .r0 DOK, .ldr .r12 .r0 DTAB,
    .dp .add .r12 .r0 (.reg .r12)] ++ pointToTable ++ loadHeader 8164 ++
  [.str .r12 .r0 DPTR, .ldr .r3 .r0 DTAB, .dp .add .r3 .r3 (.imm 128), .str .r3 .r0 DTAB,
    .movw .r2 8032, .cmp .r3 (.reg .r2)]

/-- One decoding, of the encoding at `[DPTR]`. -/
def decodeBody (umaal : Bool) : Prog isa :=
  .seq (.block [.ldr .r12 .r0 DPTR]) (.seq (pointDecode umaal) (.block decodeNext))

/-- `A` and `R` decoded, by one loop of two iterations. -/
def decodeBoth (umaal : Bool) : Prog isa := .seq (.block decodeStart) (.loop (decodeBody umaal) .ne)

/-- Both decoded, and the equation if both are points. -/
def verifyDecode (umaal : Bool) : Prog isa :=
  .seq (decodeBoth umaal) (.seq (.block [.ldr .r9 .r0 DOK, .cmp .r9 (.imm 0)])
    (.ite .ne (verifyEquationPoints umaal) recoverInvalid))

def verifyBody (umaal : Bool) : Prog isa :=
  .seq (.block verifyScalar) (.ite .eq (.seq (.block initFields) (verifyDecode umaal)) recoverInvalid)

def verifyHeaders : List Instr :=
  [.movw .r12 8160, .dp .add .r12 .r3 (.reg .r12),
    .str .r0 .r12 0, .str .r1 .r12 4, .str .r2 .r12 8, .mov .r0 (.reg .r3)]
def verifySetup : List Instr := scalarSave .r3 ++ verifyHeaders ++ scratchAddr LRS ++ [.str .lr .r12 0]
def verifyFinish : List Instr :=
  [.mov .r1 (.reg .r9)] ++ scratchAddr LRS ++ [.ldr .lr .r12 0] ++ scalarRestore ++ [.mov .r0 (.reg .r1)]
def verifyEquation (umaal : Bool) : Prog isa :=
  .seq (.block verifySetup) (.seq (verifyBody umaal) (.block verifyFinish))

end VG.Impl.Ed25519.Arm
