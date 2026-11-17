module

public import VerifiedGarbage.Impl.Ed25519.Arm.PointDecode
public import VerifiedGarbage.Impl.Ed25519.Arm.PointEqual
public import VerifiedGarbage.Impl.Ed25519.Arm.PointTableIO
public import VerifiedGarbage.Impl.Ed25519.Arm.PointFromScalar
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
def verifyLhs : Prog isa :=
  .seq (.block (loadHeader 8164 ++ [.dp .add .r12 .r12 (.imm 32)]))
    (.seq combMultiply (.block (pointTableWrite 8032)))

def verifyCombine : Prog isa :=
  .seq copyPointToQ (.seq (.block (pointTableRead 7904))
    (.seq Point16.addCall (.seq copyPointToQ (.block (pointTableRead 8032)))))

/-! ## `[k]A` on `k`'s bits, which are public

Double-and-add from the top bit: the sum (slots 0–3) is doubled for every bit, and `A`
(slots 4–7) is added only where the bit is set. The bits are the challenge's, which
verification may leak, so the branch is on public data. `r11` counts the bytes of `k` left and
`r10` holds the byte in hand in its top byte, shifted left once a bit: neither is written by the point
functions. -/

/-- The address of the next byte of `k` down (`k`'s pointer at word 52, the byte's index in
`r11`) into `r3`. -/
def bitsAddr : List Instr :=
  [.dp .sub .r11 .r11 (.imm 1), .ldr .r3 .r0 52, .dp .add .r3 .r3 (.reg .r11)]

/-- The byte at `r3` into the top byte of `r10`. -/
def bitsByte : List Instr := [.ldrb .r10 .r3 0, .mov .r10 (.shifted .r10 .lsl 24)]

/-- The next byte of `k` down into the top byte of `r10`. -/
def bitsLoad : List Instr := bitsAddr ++ bitsByte

/-- Z clear if the top bit of `r10` is set. -/
def bitTest : List Instr := [.mov .r9 (.shifted .r10 .lsr 31), .cmp .r9 (.imm 0)]

/-- One bit, the top one of the byte in `r10`: the sum doubled, `A` added if the bit is set,
and `r10` shifted. -/
def bitStep : Prog isa :=
  .seq Point16.doubleCall (.seq (.block bitTest)
    (.seq (.ite .ne Point16.addCall (.block [])) (.block [.mov .r10 (.shifted .r10 .lsl 1)])))

/-- `c`, `n` times, then `k`. -/
def repeatThen : Nat → Prog isa → Prog isa → Prog isa
  | 0, _, k => k
  | n + 1, c, k => .seq c (repeatThen n c k)

/-- A byte of `k`: its eight bits from the top. Z is set after byte 0. -/
def byteStep : Prog isa := .seq (.block bitsLoad) (repeatThen 8 bitStep (.block [.cmp .r11 (.imm 0)]))

/-- `k`'s pointer (`r12`) saved, `A` from slots 0–3 to slots 4–7, `d` in slot 16, the sum at
the identity, and 32 bytes to go. -/
def publicMulInit : Prog isa :=
  .seq (.block [.str .r12 .r0 52])
    (.seq (fieldCode (copyPointToQOps ++ [.const 16 Spec.Ed25519.d] ++ constPointOps Spec.Ed25519.identity))
      (.block [.mov .r11 (.imm 32)]))

/-- `[k]A` into slots 0–3, for `A` in slots 0–3 and the 32 bytes of `k` at `r12`. -/
def publicMul : Prog isa := .seq publicMulInit (.loop byteStep .ne)

def verifyRhs : Prog isa :=
  .seq (.block (pointTableRead 7776 ++ loadHeader 8168))
    (.seq publicMul (.seq verifyCombine pointEqual))

def verifyEquationPoints : Prog isa := .seq verifyLhs verifyRhs
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
def decodeBody : Prog isa := .seq (.block [.ldr .r12 .r0 DPTR]) (.seq pointDecode (.block decodeNext))

/-- `A` and `R` decoded, by one loop of two iterations. -/
def decodeBoth : Prog isa := .seq (.block decodeStart) (.loop decodeBody .ne)

/-- Both decoded, and the equation if both are points. -/
def verifyDecode : Prog isa :=
  .seq decodeBoth (.seq (.block [.ldr .r9 .r0 DOK, .cmp .r9 (.imm 0)])
    (.ite .ne verifyEquationPoints recoverInvalid))

def verifyBody : Prog isa :=
  .seq (.block verifyScalar) (.ite .eq (.seq (.block initFields) verifyDecode) recoverInvalid)

def verifyHeaders : List Instr :=
  [.movw .r12 8160, .dp .add .r12 .r3 (.reg .r12),
    .str .r0 .r12 0, .str .r1 .r12 4, .str .r2 .r12 8, .mov .r0 (.reg .r3)]
def verifySetup : List Instr := scalarSave .r3 ++ verifyHeaders ++ scratchAddr LRS ++ [.str .lr .r12 0]
def verifyFinish : List Instr :=
  [.mov .r1 (.reg .r9)] ++ scratchAddr LRS ++ [.ldr .lr .r12 0] ++ scalarRestore ++ [.mov .r0 (.reg .r1)]
def verifyEquation : Prog isa :=
  .seq (.block verifySetup) (.seq verifyBody (.block verifyFinish))

end VG.Impl.Ed25519.Arm
