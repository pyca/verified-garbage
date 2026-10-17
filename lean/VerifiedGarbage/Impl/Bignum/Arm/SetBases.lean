module

public import VerifiedGarbage.Impl.Bignum.Arm.Store64

/-! # Populate the shared RSA header's array pointers

r0 walks the eight 64-bit header slots, r4 walks the array bases, r5 is the
array stride, r3 is zero, and lr counts the remaining pointers.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def setBaseStep : List Instr := store64 .r4 .r3 .r0 0 ++
  [.dp .add .r0 .r0 (.imm 8), .dp .add .r4 .r4 (.reg .r5), .subs .lr .lr (.imm 1)]

def setBases : Prog isa := .loop (.block setBaseStep) .ne

end VG.Impl.Bignum.Arm
