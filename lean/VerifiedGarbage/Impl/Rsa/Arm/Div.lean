module

public import VerifiedGarbage.Impl.Bignum.Arm.ShiftLeft
public import VerifiedGarbage.Impl.Bignum.Arm.SubtractIfGe
public import VerifiedGarbage.Impl.Bignum.Arm.Zero

/-! # Fixed-iteration native-word division for RSA key operations

`r8` points to a public control header: quotient, remainder, divisor and
temporary pointers at offsets 0, 4, 8, 12, and the quotient's native-word
count at 16. Remainder, divisor and temporary have one additional word.
The divisor's additional word is zero. Only the array contents are secret.
The iteration counter is `r6`; all word loops preserve it and `r8`.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Bignum.Arm

def quotientArgs : List Instr :=
  [.ldr .r0 .r8 0, .ldr .lr .r8 16, .mov .r11 (.imm 0)]
def remainderArgs : List Instr :=
  [.ldr .r0 .r8 4, .ldr .lr .r8 16, .dp .add .lr .lr (.imm 1)]
def subtractArgs : List Instr :=
  [.ldr .r0 .r8 12, .ldr .r10 .r8 4, .ldr .r12 .r8 8,
   .mov .r9 (.reg .r10), .ldr .r7 .r8 16, .dp .add .r7 .r7 (.imm 1),
   .mov .lr (.reg .r7), .mov .r11 (.imm 0)]
def quotientBit : List Instr :=
  [.ldr .r0 .r8 0, .ldr .r3 .r0 0, .dp .eor .r11 .r11 (.imm 1),
   .dp .add .r3 .r3 (.reg .r11), .str .r3 .r0 0, .subs .r6 .r6 (.imm 1)]

def shift : Prog isa :=
  .seq (.block quotientArgs) (.seq shiftLeft (.seq (.block remainderArgs) shiftLeft))
def reduce : Prog isa := .seq (.block subtractArgs) subtractIfGe

def step : Prog isa := .seq shift (.seq reduce (.block quotientBit))

def init : Prog isa :=
  .seq (.block (remainderArgs ++ [.mov .r3 (.imm 0)]))
    (.seq zero (.block [.ldr .r6 .r8 16, .mov .r6 (.shifted .r6 .lsl 5)]))

/-- `32 n` division steps. For a nonzero divisor the final arrays contain
the quotient and remainder; a zero divisor still has a fixed, safe trace. -/
def code : Prog isa := .seq init (.loop step .ne)

end VG.Impl.Rsa.Arm.Div
