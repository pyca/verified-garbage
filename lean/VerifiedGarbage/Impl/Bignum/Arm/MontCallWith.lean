module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCall

/-! Callable Montgomery arithmetic with a supplied verified dispatcher. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.MontCallWith
open VG VG.Arm

def code (arithmetic : Prog isa) : Prog isa := .frame (.push MontCall.savedRegs)
  (.seq (.block [.ldrSp .r12 40]) (.seq arithmetic (.block MontCall.restore))) (.pop .r12 40)

end VG.Impl.Bignum.Arm.MontCallWith
