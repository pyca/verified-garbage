module

public import VerifiedGarbage.Impl.Bignum.Arm.SetSmallFn
public import VerifiedGarbage.Impl.Bignum.Arm.DoubleLoop

/-! # RSA Montgomery R-squared precomputation

Initialize array 4 to one, array 7 to two, then perform 128*w modular
doublings for the shared radix R=2^(64*w). All loop bounds are public.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def smallConstArgs (o value : BitVec 32) : List Instr := [.mov .r2 (.imm o), .mov .r5 (.imm value)]
def smallConst (o value : BitVec 32) : Prog isa := .seq (.block (smallConstArgs o value)) setSmallFn

def r2Constants : Prog isa := .seq (smallConst 4 1) (smallConst 7 2)
def r2CountInit : List Instr := [.ldr .r1 .r0 48, .mov .r1 (.shifted .r1 .lsl 7), .str .r1 .r0 208]
def r2Init : Prog isa := .seq r2Constants (.block r2CountInit)
def r2 : Prog isa := .seq r2Init doubleLoop

end VG.Impl.Bignum.Arm
