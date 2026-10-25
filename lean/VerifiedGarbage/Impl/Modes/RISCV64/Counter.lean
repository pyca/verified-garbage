module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-! # Big-endian counter increments on RISC-V: of 128 bits, and of GCM's last 32 -/

@[expose] public section

namespace VG.Impl.Modes.RISCV64

open VG.RISCV64

/-- One byte of a big-endian increment: the byte at `base + off` plus the
carry in `t1`, and the carry out (the sum's ninth bit) to `t1`. -/
def incByte (base : Reg) (off : Nat) : List Instr :=
  [.load .b .t0 base off, .add .t0 .t0 .t1, .store .b .t0 base off, .shift .srl .d .t1 .t0 8]

/-- Increment the `w`-byte big-endian counter at `base + off`, a byte at a
time from the last, using only `t0` and `t1`, with no branch. -/
def incBE (w : Nat) (base : Reg) (off : Nat) : List Instr :=
  .li .t1 1 :: (List.range w).flatMap fun i => incByte base (off + (w - 1 - i))

/-- Increment the 128-bit big-endian counter at `base + off`. -/
def incAt (base : Reg) (off : Nat) : List Instr := incBE 16 base off

/-- Increment the 32-bit big-endian word at `base + off` modulo 2³² (GCM's
`inc₃₂` on a counter block's last word). -/
def inc32At (base : Reg) (off : Nat) : List Instr := incBE 4 base off

end VG.Impl.Modes.RISCV64
