module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Point

/-!
# Ed25519 on RISC-V: scalar multiplication

The PPC64LE schedule (`Impl/Ed25519/PPC64LE/PointMul.lean`, ARMv7's): the
powers `[2^(16 j)] P` into a table at 1632, then for each batch of 16 bits
from the top, the batch's powers `[2^i] Q` of its checkpoint into a table at
5728, and the accumulator plus each power, kept or discarded by the bit with
a mask, constant time. The table index is `s2`, the doubling counter `s1`,
the batch counter `s6` and the scalar's pointer `s5` (`s0` on entry); all
are callee-saved, which the calls never write. The tables lie beyond the
immediates of loads and stores, so their addresses are built with `li32`;
their entries are copied a word at a time through a pointer in `s0`
(`packField`, `unpackField`).
-/

@[expose] public section

namespace VG.Impl.Ed25519.RISCV64
open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.X25519.RISCV64 (cswap)

/-- Where the batch's bits are, one per byte. -/
def BITSB : Nat := 32

/-! ## Tables -/

/-- A point (slots 0–3) to the 128 bytes at `s0`. -/
def pointToTable : List Instr := (List.range 4).flatMap fun j => packField .s0 (64 + 32 * j) (32 * j)

/-- The 128 bytes at `s0` to a point (slots 0–3). -/
def pointFromTable : List Instr := (List.range 4).flatMap fun j => unpackField .s0 (64 + 32 * j) (32 * j)

/-- Entry `s2` (128 bytes each) of the table at `start`, into `s0`. -/
def tableAddr (start : Nat) : List Instr :=
  li32 .s0 (BitVec.ofNat 32 start) ++ [.add .s0 .a3 .s0, .shift .sll .d .a4 .s2 7, .add .s0 .s0 .a4]

/-! ## Doublings and powers -/

def doubleBody : Prog isa := .seq doubleCall (.block [.addi .s1 .s1 (-1)])

def double16 : Prog isa := .seq (.block [.li .s1 16]) (.loop doubleBody (.nonzero .s1))

/-- The next entry, and `a4` zero after the last. -/
def powersNext (count : Nat) : List Instr := [.addi .s2 .s2 1, .addi .a4 .s2 (-(count : Int))]

def powerStride (batch : Bool) : Nat := if batch then 16 else 1

def powerBatch (batch : Bool) : Prog isa := if batch then double16 else doubleCall

def powersBody (start count : Nat) (batch : Bool := true) : Prog isa :=
  .seq (.block (tableAddr start ++ pointToTable))
    (.seq (powerBatch batch) (.block (powersNext count)))

def pointPowers (start count : Nat) (batch : Bool := true) : Prog isa :=
  .seq (.block [.li .s2 0]) (.loop (powersBody start count batch) (.nonzero .a4))

/-! ## Accumulation -/

/-- The mask `bit - 1` of the batch's bit `s2` into `t0`: zero to keep the
sum, all ones to restore the saved point. -/
def scalarBitMask : List Instr :=
  [.add .a4 .a3 .s2, .load .b .a4 .a4 BITSB, .addi .t0 .a4 (-1)]

def swapFields (ops : List (Slot × Slot)) : List Instr :=
  ops.flatMap fun (a, b) => cswap (offset a) (offset b)

def pointSelectPairs : List (Slot × Slot) := [(0, 17), (1, 18), (2, 19), (3, 20)]

/-- `t0` is all ones to restore the saved point, zero to retain the current point. -/
def pointSelect : List Instr := swapFields pointSelectPairs

def prepareAdd : Prog isa :=
  .seq savePoint (.seq (.block (tableAddr 5728 ++ pointFromTable))
    (.seq copyPointToQ restorePoint))

def pointAccumulate : Prog isa :=
  .seq prepareAdd (.seq addCall (.block (scalarBitMask ++ pointSelect)))

def accumulateBody : Prog isa := .seq (.block [.addi .s2 .s2 (-1)]) pointAccumulate

def accumulate16 : Prog isa :=
  .seq (.block [.li .s2 16]) (.loop accumulateBody (.nonzero .s2))

/-! ## Batches -/

def loadCheckpoint : Prog isa := .seq savePoint (.block (tableAddr 1632 ++ pointFromTable))

def prepareBatch : Prog isa := .seq loadCheckpoint (.seq (pointPowers 5728 16 false) restorePoint)

/-- Bit `k` of the batch's 16 bits in `a4`, into byte `BITSB + k`. -/
def expandBit (k : Nat) : List Instr :=
  [.shift .sll .d .a5 .a4 (63 - k), .shift .srl .d .a5 .a5 63, .store .b .a5 .a3 (BITSB + k)]

def expandBits : List Instr := (List.range 16).flatMap expandBit

/-- The batch's 16 bits: bytes `2c` and `2c + 1` of the scalar, `c` the
batch counter. -/
def batchDigit : List Instr :=
  [.shift .sll .d .a4 .s6 1, .add .s0 .s5 .a4, .load .b .a4 .s0 0, .load .b .a5 .s0 1,
    .shift .sll .d .a5 .a5 8, .add .a4 .a4 .a5]

def batchBits : List Instr := batchDigit ++ expandBits

/-- The next batch, from the top: its index into `s6` and `s2` (which
the checkpoint's table entry is read at). -/
def batchStart : List Instr := [.addi .s6 .s6 (-1), .addi .s2 .s6 0]

def pointMulBody : Prog isa :=
  .seq (.block batchStart) (.seq prepareBatch (.seq (.block batchBits) accumulate16))

def pointMultiply (count : Nat) : Prog isa :=
  .seq (pointPowers 1632 count true)
    (.seq (constPoint Spec.Ed25519.identity)
      (.seq (.block [.li .s6 count]) (.loop pointMulBody (.nonzero .s6))))

/-- `[s] P` for the point `P` in slots 0–3 and the scalar of `2 count`
bytes at `s0`. -/
def pointFromScalar (count : Nat) : Prog isa :=
  .seq (.block [.addi .s5 .s0 0]) (.seq (fieldCode [.const 16 Spec.Ed25519.d]) (pointMultiply count))

end VG.Impl.Ed25519.RISCV64
