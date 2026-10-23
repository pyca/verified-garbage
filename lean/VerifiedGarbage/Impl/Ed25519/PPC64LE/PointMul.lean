module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Packed
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Point

/-!
# Ed25519 on PPC64LE: scalar multiplication

ARMv7's schedule (`Impl/Ed25519/Arm/PointMul.lean` and the files it
builds on): the powers `[2^(16 j)] P` into a table at 1632, then for each
batch of 16 bits from the top, the batch's powers `[2^i] Q` of its
checkpoint into a table at 5728, and the accumulator plus each power,
kept or discarded by the bit with a mask, constant time. The table index is
`r16`, the doubling counter `r15`, the batch counter `r26` and the scalar's
pointer `r19` (`r14` on entry); all are nonvolatile, which the calls never
write.
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE
open VG.PPC64LE

/-! ## Tables -/

def scratchAddr (o : Nat) : List Instr := [.addi .r14 .r6 o]

def pointTableWrite (o : Nat) : List Instr := scratchAddr o ++ pointToTable

def pointTableRead (o : Nat) : List Instr := scratchAddr o ++ pointFromTable

/-- Entry `r16` (128 bytes each) of the table at `start`, into `r14`. -/
def tableAddr (start : Nat) : List Instr :=
  [.addi .r14 .r6 start, .lsl .r7 .r16 7, .add .r14 .r14 .r7]

/-! ## Doublings and powers -/

def doubleBody : Prog isa := .seq doubleCall (.block [.subi .r15 .r15 1])

def double16 : Prog isa := .seq (.block [.li .r15 16]) (.loop doubleBody (.nonzero .d .r15))

/-- The next entry, and `r7` zero after the last. -/
def powersNext (count : Nat) : List Instr := [.addi .r16 .r16 1, .subi .r7 .r16 count]

def powerStride (batch : Bool) : Nat := if batch then 16 else 1

def powerBatch (batch : Bool) : Prog isa := if batch then double16 else doubleCall

def powersBody (start count : Nat) (batch : Bool := true) : Prog isa :=
  .seq (.block (tableAddr start ++ pointToTable))
    (.seq (powerBatch batch) (.block (powersNext count)))

def pointPowers (start count : Nat) (batch : Bool := true) : Prog isa :=
  .seq (.block [.li .r16 0]) (.loop (powersBody start count batch) (.nonzero .d .r7))

/-! ## Accumulation -/

/-- The mask `bit - 1` of the batch's bit `r16` into `r11`: zero to keep the
sum, all ones to restore the saved point. -/
def scalarBitMask : List Instr :=
  [.add .r7 .r6 .r16, .lbz .r7 .r7 BITSB, .subi .r11 .r7 1]

def swapFields (ops : List (Slot × Slot)) : List Instr :=
  ops.flatMap fun (a, b) => cswap (offset a) (offset b)

def pointSelectPairs : List (Slot × Slot) := [(0, 17), (1, 18), (2, 19), (3, 20)]

/-- `r11` is all ones to restore the saved point, zero to retain the current point. -/
def pointSelect : List Instr := swapFields pointSelectPairs

def prepareAdd : Prog isa :=
  .seq savePoint (.seq (.block (tableAddr 5728 ++ pointFromTable))
    (.seq copyPointToQ restorePoint))

def pointAccumulate : Prog isa :=
  .seq prepareAdd (.seq addCall (.block (scalarBitMask ++ pointSelect)))

def accumulateBody : Prog isa := .seq (.block [.subi .r16 .r16 1]) pointAccumulate

def accumulate16 : Prog isa :=
  .seq (.block [.li .r16 16]) (.loop accumulateBody (.nonzero .d .r16))

/-! ## Batches -/

def loadCheckpoint : Prog isa := .seq savePoint (.block (tableAddr 1632 ++ pointFromTable))

def prepareBatch : Prog isa := .seq loadCheckpoint (.seq (pointPowers 5728 16 false) restorePoint)

/-- Bit `k` of the batch's 16 bits in `r7`, into byte `BITSB + k`. -/
def expandBit (k : Nat) : List Instr :=
  [.lsl .r8 .r7 (63 - k), .lsr .d .r8 .r8 63, .stb .r8 .r6 (BITSB + k)]

def expandBits : List Instr := (List.range 16).flatMap expandBit

/-- The batch's 16 bits: bytes `2c` and `2c + 1` of the scalar, `c` the
batch counter. -/
def batchDigit : List Instr :=
  [.lsl .r7 .r26 1, .add .r14 .r19 .r7, .lbz .r7 .r14 0, .lbz .r8 .r14 1, .lsl .r8 .r8 8,
    .add .r7 .r7 .r8]

def batchBits : List Instr := batchDigit ++ expandBits

/-- The next batch, from the top: its index into `r26` and `r16` (which
the checkpoint's table entry is read at). -/
def batchStart : List Instr := [.subi .r26 .r26 1, .addi .r16 .r26 0]

def pointMulBody : Prog isa :=
  .seq (.block batchStart) (.seq prepareBatch (.seq (.block batchBits) accumulate16))

def pointMultiply (count : Nat) : Prog isa :=
  .seq (pointPowers 1632 count true)
    (.seq (constPoint Spec.Ed25519.identity)
      (.seq (.block [.li .r26 count]) (.loop pointMulBody (.nonzero .d .r26))))

/-- `[s] P` for the point `P` in slots 0–3 and the scalar of `2 count`
bytes at `r14`. -/
def pointFromScalar (count : Nat) : Prog isa :=
  .seq (.block [.addi .r19 .r14 0]) (.seq (fieldCode [.const 16 Spec.Ed25519.d]) (pointMultiply count))

end VG.Impl.Ed25519.PPC64LE
