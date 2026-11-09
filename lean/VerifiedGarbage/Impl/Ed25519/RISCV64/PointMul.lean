module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.FieldMemory
public import VerifiedGarbage.Spec.Ed25519

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

end VG.Impl.Ed25519.RISCV64
