module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallWith
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline
public import VerifiedGarbage.Impl.Bignum.Arm.Fios2

/-! The two-row UMAAL round through the existing callable ABI. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.MontCallFios2
open VG VG.Arm VG.Impl.Bignum.Arm

def arithmetic : Prog isa := MontPipeline.fnBody Fios2.round

def code : Prog isa := MontCallWith.code arithmetic

end VG.Impl.Bignum.Arm.MontCallFios2
