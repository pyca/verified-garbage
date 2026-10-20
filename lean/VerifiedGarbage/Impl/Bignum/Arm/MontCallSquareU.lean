module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallWith
public import VerifiedGarbage.Impl.Bignum.Arm.SquareUmaal

/-! One shared helper uses the UMAAL diagonal square and RSA multiplication. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.MontCallSquareU
open VG VG.Arm

def arithmetic : Prog isa := MontCallWith.dispatch squareBodyU MontFn.body

def code : Prog isa := MontCallWith.code arithmetic

end VG.Impl.Bignum.Arm.MontCallSquareU
