module

public import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc

/-! Public Montgomery interface on AArch64: CIOS products and symmetric squares with blocked reduction. -/

@[expose] public section

namespace VG.Impl.Bignum.AArch64.Public
open VG VG.AArch64

def mm (o a b : Nat) : Prog isa := BlockedRedc.mm o a b

end VG.Impl.Bignum.AArch64.Public
