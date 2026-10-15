module

public import VerifiedGarbage.Impl.Bignum.Arm.Csub

/-! # Fixed-width conditional subtraction, including in-place reduction -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- Subtract `r12` from `r10` into temporary `r0`, then select the difference
or original into `r9`. All arrays have `r7 = lr` nonzero native words;
`r11` initially holds zero and returns the borrow bit. The destination may
be the original input, but the temporary is separate from both inputs. -/
def subtractIfGe : Prog isa :=
  .seq subRow (.seq (.block selectPrepare) selectRow)

end VG.Impl.Bignum.Arm
