module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallWith
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline
public import VerifiedGarbage.Impl.Bignum.Arm.Fios

/-! One fused Montgomery kernel handles products and squares through the existing callable ABI. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.MontCallFios
open VG VG.Arm VG.Impl.Bignum.Arm

def arithmetic : Prog isa := MontPipeline.fnBody Fios.round

def code : Prog isa := MontCallWith.code arithmetic

end VG.Impl.Bignum.Arm.MontCallFios
