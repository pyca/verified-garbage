module

public import VerifiedGarbage.Impl.Bignum.Arm.MontFn

/-! The native Montgomery setup and finish accept any verified scanning round. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm

def rounds (round : Prog isa) : Prog isa := .loop round .ne

def core (round : Prog isa) : Prog isa := .seq (rounds round) montFinish

def body (round : Prog isa) : Prog isa := .seq montInit (core round)

def fnBody (round : Prog isa) : Prog isa := .seq (.block MontFn.bases) (body round)

end VG.Impl.Bignum.Arm.MontPipeline
