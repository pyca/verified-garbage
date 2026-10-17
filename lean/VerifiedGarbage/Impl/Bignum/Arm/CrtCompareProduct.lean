module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtClearWide
public import VerifiedGarbage.Impl.Bignum.Arm.EqualBuffers

/-! # Compare the complete factor product with the padded modulus -/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def comparePointers : List Instr := [.ldr .r10 .r0 232, .ldr .r12 .r0 240]
def compareArgs : Prog isa := .seq (.block comparePointers) (.block (clearWideArgs 236))
def compareProduct : Prog isa := .seq compareArgs (.seq equalBuffers (.block [.ldrSp .r0 0]))

end VG.Impl.Bignum.Arm.Crt
