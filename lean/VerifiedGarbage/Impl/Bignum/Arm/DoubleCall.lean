module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Impl.Bignum.Arm.DoubleLoop

/-! # One callable modular doubling

The callee takes the arguments of the callable Montgomery product
(`MontCall`): the workspace in r0, its length in r1, the output and scalar
indices in r2 and r3 and the operand index in the caller's stack word. The
scalar array starts with 2. Each repetition of R-squared's doubling loop
calls it, so the doubling has one copy rather than one in every caller.
-/

@[expose] public section
namespace VG.Impl.Bignum.Arm.DoubleCall
open VG VG.Arm

def code : Prog isa := .frame (.push MontCall.savedRegs)
  (.seq (.block [.ldrSp .r12 40]) (.seq doubleFnBody (.block MontCall.restore))) (.pop .r12 40)

/-- R-squared's doublings, each by `dbl` (which leaves the workspace in r0),
counted down at header byte 208. `loop doubleLoopMultiply` is `doubleLoop`. -/
def loop (dbl : Prog isa) : Prog isa := .loop (.seq dbl (.block doubleCount)) .ne

end VG.Impl.Bignum.Arm.DoubleCall
