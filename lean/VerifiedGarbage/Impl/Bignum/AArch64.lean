module

public import VerifiedGarbage.Impl.Bignum.AArch64.SquareCall

/-! Public Montgomery interface on AArch64: CIOS products and symmetric squares with blocked reduction. -/

@[expose] public section

namespace VG.Impl.Bignum.AArch64.Public
open VG VG.AArch64

def mm (o a b : Nat) : Prog isa := SquareCall.mm o a b

end VG.Impl.Bignum.AArch64.Public
