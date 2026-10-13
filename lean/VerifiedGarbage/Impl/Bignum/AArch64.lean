module

public import VerifiedGarbage.Impl.Bignum.AArch64.Square

/-! Public Montgomery interface on AArch64: CIOS products and symmetric squares. -/

@[expose] public section

namespace VG.Impl.Bignum.AArch64.Public
open VG VG.AArch64

def mm (o a b : Nat) : Prog isa := Square.montMul o a b

end VG.Impl.Bignum.AArch64.Public
