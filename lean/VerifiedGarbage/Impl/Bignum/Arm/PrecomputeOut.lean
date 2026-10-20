module

public import VerifiedGarbage.Impl.Bignum.Arm.ExportArray

/-! # Export modulus and R-squared to the public RSA precomputation buffer

r0 is the workspace and r4 is the output pointer. Returns one in r0.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def precomputeOutAdvance : List Instr :=
  [.ldr .r1 .r0 48, .mov .r1 (.shifted .r1 .lsl 3), .dp .add .r4 .r4 (.reg .r1), .mov .r2 (.imm 4)]
def precomputeOut : Prog isa := .seq (.block [.mov .r2 (.imm 0)])
  (.seq exportArray (.seq (.block precomputeOutAdvance) (.seq exportArray (.block [.mov .r0 (.imm 1)]))))

end VG.Impl.Bignum.Arm
