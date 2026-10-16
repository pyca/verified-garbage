module

public import VerifiedGarbage.Impl.Bignum.Arm.MontBody

/-! # ARMv7 callable Montgomery multiplication

The public indices address 64-bit header slots; their low words are native
pointers. Arithmetic uses two packed 32-bit words per 64-bit RSA word.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.MontFn
open VG VG.Arm

def loadArray (d i : Reg) : List Instr :=
  [.dp .add i .r0 (.shifted i .lsl 3), .ldr d i 64]

def basesTail : List Instr :=
  [.ldr .r5 .r0 88, .ldr .r6 .r0 80, .ldr .r7 .r0 48,
   .dp .add .r7 .r7 (.reg .r7), .ldr .r11 .r0 64, .ldr .r12 .r0 56]

def bases : List Instr :=
  loadArray .r10 .r2 ++ loadArray .r8 .r3 ++ loadArray .r9 .r12 ++ basesTail

def body : Prog isa := .seq (.block bases) montBody

def restore : List Instr :=
  [.ldrSp .r5 4, .ldrSp .r6 8, .ldrSp .r7 12, .ldrSp .r8 16,
   .ldrSp .r9 20, .ldrSp .r10 24, .ldrSp .r11 28, .ldrSp .lr 32]

def mul : Prog isa :=
  .frame (.push [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr])
    (.seq (.block [.ldrSp .r12 36]) (.seq body (.block restore))) (.pop .r4 36)

end VG.Impl.Bignum.Arm.MontFn
