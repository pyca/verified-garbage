module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # In-place shifts by `k` bits, `0 < k < 32`

`lr` words at `r0`, least significant first, are shifted in place by an
immediate number of bits `k` in one pass. The count `lr` is public and
nonzero; the words may be secret, and `k` is part of the code.

* `shiftRightK k`: word `i` becomes bits `k`–`k + 31` of words `i` and
  `i + 1`, so the low `k` bits of the word after them come in at the top.
  Each word is read before the store to the word below it, so the shift
  runs upwards in place. `r3` and `r4` are scratch.
* `shiftLeftK k`: `r11` (below `2^k`) comes in at the bottom and the top `k`
  bits go out in `r11`. `r3` and `r4` are scratch.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def shiftRightKStep (k : Nat) : List Instr :=
  [.ldr .r3 .r0 0, .ldr .r4 .r0 4, .mov .r3 (.shifted .r3 .lsr k),
   .dp .add .r3 .r3 (.shifted .r4 .lsl (32 - k)), .str .r3 .r0 0,
   .dp .add .r0 .r0 (.imm 4), .subs .lr .lr (.imm 1)]

def shiftRightK (k : Nat) : Prog isa := .loop (.block (shiftRightKStep k)) .ne

/-- The shifted word has its low `k` bits zero, so adding the incoming bits does not carry. -/
def shiftLeftKStep (k : Nat) : List Instr :=
  [.ldr .r4 .r0 0, .dp .add .r3 .r11 (.shifted .r4 .lsl k),
   .mov .r11 (.shifted .r4 .lsr (32 - k)), .str .r3 .r0 0,
   .dp .add .r0 .r0 (.imm 4), .subs .lr .lr (.imm 1)]

def shiftLeftK (k : Nat) : Prog isa := .loop (.block (shiftLeftKStep k)) .ne

end VG.Impl.Bignum.Arm
