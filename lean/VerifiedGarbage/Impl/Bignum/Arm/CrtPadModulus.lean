module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtClearWide
public import VerifiedGarbage.Impl.Bignum.Arm.ExportArray

/-! # Extend the modulus to the full factor-product width -/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def padModulusArgs : List Instr := [.ldr .r4 .r0 240, .mov .r2 (.imm 0)]
def padModulus : Prog isa := .seq (clearWide 240) (.seq (.block padModulusArgs) exportArray)

end VG.Impl.Bignum.Arm.Crt
