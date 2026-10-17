module

public import VerifiedGarbage.Impl.Bignum.Arm.Mul64
public import VerifiedGarbage.Impl.Bignum.Arm.Sub64

/-! # Newton iteration on 64-bit register pairs

r0 points to the odd 64-bit modulus word; r10:r1 holds the approximation.
The update is x := x * (2 - m*x) modulo 2^64, using no long multiply.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def newton64Load : List Instr := [.ldr .r2 .r0 0, .ldr .r11 .r0 4]
def newton64Subtract : List Instr := [.mov .r6 (.imm 2)] ++ sub64
def newton64Finish : List Instr := [.mov .r1 (.reg .r3), .mov .r10 (.reg .r4)]
def newton64 : List Instr := newton64Load ++ mul64 ++ newton64Subtract ++ mul64 ++ newton64Finish

end VG.Impl.Bignum.Arm
