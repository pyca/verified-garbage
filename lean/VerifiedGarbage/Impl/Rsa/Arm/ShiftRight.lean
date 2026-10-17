module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Runtime-length in-place one-bit right shift

`lr` words at `r0`, least significant first, are shifted right by one bit in
place: word `i` becomes bits 1–32 of words `i` and `i + 1`, so the low bit
of the word after them comes in at the top. Each word is read before the
store to the word below it, so the shift runs upwards in place. The count is
public and nonzero; `r3` and `r4` are scratch.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm
open VG VG.Arm

def shiftRightStep : List Instr :=
  [.ldr .r3 .r0 0, .ldr .r4 .r0 4, .mov .r3 (.shifted .r3 .lsr 1),
   .dp .add .r3 .r3 (.shifted .r4 .lsl 31), .str .r3 .r0 0,
   .dp .add .r0 .r0 (.imm 4), .subs .lr .lr (.imm 1)]

def shiftRight : Prog isa := .loop (.block shiftRightStep) .ne

end VG.Impl.Rsa.Arm
