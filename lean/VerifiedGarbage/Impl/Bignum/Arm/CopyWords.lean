module

public import VerifiedGarbage.Impl.Bignum.Arm.Select

/-! Word copies avoid the duplicate load and mask arithmetic of selection.
The legacy row cursor and mask setup are retained for the shared row invariant. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def copyWord : Prog isa := .block [.ldr .r1 .r10 0, .str .r1 .r0 0]
def copyWordBody : Prog isa := .seq copyWord (.block subAdvance)
def copyWords : Prog isa := .seq (.block selectMask) (.loop copyWordBody .ne)

end VG.Impl.Bignum.Arm
