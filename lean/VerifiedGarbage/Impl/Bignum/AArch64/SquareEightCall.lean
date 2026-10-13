module

public import VerifiedGarbage.Impl.Bignum.AArch64.SquareCall

public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightDispatch

/-! Share the scheduled squares while preserving the caller's return address.
The guarded body's fallback is inline, so it cannot overwrite the saved link. -/

@[expose] public section
namespace VG.Impl.Bignum.AArch64.SquareEightCall
open VG VG.AArch64

def mm (o a b : Nat) : Prog isa :=
  if o = a ∧ a = b ∧ o = 6 then
    SquareCall.call s!"vg_rsa_square_{o}_{o}" (SquareEightDispatch.mm o o o)
  else SquareCall.mm o a b

end VG.Impl.Bignum.AArch64.SquareEightCall
