module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Check the shared RSA modulus limits before precomputation

r4 points at k big-endian bytes and r6 is k, with 64 <= k <= 1024.
The zero flag is true exactly when the modulus is valid. Memory is unchanged.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def modulusCheckRead : List Instr :=
  [.ldrb .r1 .r4 0, .dp .add .r2 .r4 (.reg .r6), .dp .sub .r2 .r2 (.imm 1), .ldrb .r2 .r2 0]

def modulusCheckBounds : List Instr :=
  [.dp .sub .r7 .r1 (.imm 1), .mov .r7 (.shifted .r7 .lsr 31),
   .dp .sub .r9 .r6 (.imm 64), .mov .r9 (.shifted .r9 .lsl 8), .dp .add .r9 .r9 (.reg .r1),
   .dp .sub .r9 .r9 (.imm 128), .mov .r9 (.shifted .r9 .lsr 31)]

def modulusCheckFinish : List Instr :=
  [.dp .and .r2 .r2 (.imm 1), .dp .eor .r2 .r2 (.imm 1),
   .dp .orr .r7 .r7 (.reg .r2), .dp .orr .r7 .r7 (.reg .r9), .subs .r7 .r7 (.imm 0)]

def modulusCheckCalc : List Instr := modulusCheckBounds ++ modulusCheckFinish

def modulusCheck : List Instr := modulusCheckRead ++ modulusCheckCalc

end VG.Impl.Bignum.Arm
