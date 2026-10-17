module

public import VerifiedGarbage.Impl.Bignum.Arm.Newton64

/-! # Negative inverse of an odd 64-bit word

Five Newton iterations from x=m, followed by negation, leave -m^-1 in
r11:r2. r0 points to m, and the instruction sequence preserves memory.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def minv64Start : List Instr := newton64Load ++ [.mov .r1 (.reg .r2), .mov .r10 (.reg .r11)]
def minv64End : List Instr :=
  [.mov .r3 (.reg .r1), .mov .r4 (.reg .r10), .mov .r6 (.imm 0)] ++ sub64

def minv64 : List Instr := minv64Start ++ newton64 ++ newton64 ++ newton64 ++ newton64 ++ newton64 ++ minv64End

end VG.Impl.Bignum.Arm
