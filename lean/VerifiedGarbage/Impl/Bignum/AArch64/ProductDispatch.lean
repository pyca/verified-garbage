module

public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightCall

@[expose] public section
namespace VG.Impl.Bignum.AArch64.ProductDispatch
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

/-- The eight-limb product keeps the existing path for squares, unsupported
widths, and output aliases of the modulus. -/
def guarded (o a b : Nat) : Prog isa :=
 .seq (.block [ldh .x12 sW, .lsr .x .x3 .x12 4, movi .x4 7, .logic .and .x .x4 .x12 .x4])
  (.ite (.nonzero .x .x3)
    (.ite (.zero .x .x4) (ProductEight.multiply o a b) (SquareEightCall.mm o a b))
    (SquareEightCall.mm o a b))

def mm (o a b : Nat) : Prog isa :=
 if a ≠ b ∧ o ≠ Public.aN then guarded o a b else SquareEightCall.mm o a b

end VG.Impl.Bignum.AArch64.ProductDispatch
