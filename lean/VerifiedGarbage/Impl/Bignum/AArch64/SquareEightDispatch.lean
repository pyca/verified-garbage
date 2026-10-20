module

public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightRaw

@[expose] public section
namespace VG.Impl.Bignum.AArch64.SquareEightDispatch
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

/-- Preserve all existing width and alias fallbacks. -/
def guarded (o a : Nat) : Prog isa :=
 .seq (.block [ldh .x12 sW, .lsr .x .x3 .x12 4, movi .x4 7, .logic .and .x .x4 .x12 .x4])
  (.ite (.nonzero .x .x3)
    (.ite (.zero .x .x4) (SquareEightRaw.square o a) (BlockedRedc.mm o a a))
    (BlockedRedc.mm o a a))
def mm (o a b : Nat) : Prog isa :=
 if a = b ∧ o ≠ Public.aN then guarded o a else BlockedRedc.mm o a b

end VG.Impl.Bignum.AArch64.SquareEightDispatch
