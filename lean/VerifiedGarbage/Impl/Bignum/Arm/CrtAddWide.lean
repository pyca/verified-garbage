module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtClearWide
public import VerifiedGarbage.Impl.Bignum.Arm.RowFull

/-! # Add the padded q residue to the full recombination product -/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def addWideScalars : List Instr :=
  [.dp .sub .lr .lr (.imm 2), .mov .r1 (.imm 1), .mov .r11 (.imm 0)]
def addWideArgs : Prog isa := .seq (.block [.ldr .r12 .r0 240])
  (.seq (.block (clearWideArgs 232)) (.block addWideScalars))
def addWide : Prog isa := .seq addWideArgs (.seq rowFull (.block [.ldrSp .r0 0]))

end VG.Impl.Bignum.Arm.Crt
