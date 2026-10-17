module

public import VerifiedGarbage.Impl.Bignum.Arm.SelectArray
public import VerifiedGarbage.Impl.Bignum.Arm.R2

/-! # Replace a rejected secret modulus with three, without a branch

The validation bit is stored at header offset 212. Array 7 is scratch.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def sanitizeBit : List Instr := [.ldr .r11 .r0 212]
def sanitizeModulus : Prog isa :=
  .seq (smallConst 7 3) (.seq (.block sanitizeBit) (selectArray 0 7 0))

end VG.Impl.Bignum.Arm
