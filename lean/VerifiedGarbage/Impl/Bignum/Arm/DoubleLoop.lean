module

public import VerifiedGarbage.Impl.Bignum.Arm.DoubleFnBody

/-! # Repeated modular doubling of the RSA R-squared array

The scalar 2 is in array 7 and the operand/result in array 4. The public
remaining count is in header byte 208. The outer frame saves r0 at sp.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def doubleIndices : List Instr := [.mov .r2 (.imm 4), .mov .r3 (.imm 7), .mov .r12 (.imm 4)]
def doubleCount : List Instr := [.ldr .r1 .r0 208, .subs .r1 .r1 (.imm 1), .str .r1 .r0 208]
def doubleLoopMultiply : Prog isa := .seq (.block doubleIndices) doubleFnRestore
def doubleLoopBody : Prog isa := .seq doubleLoopMultiply (.block doubleCount)
def doubleLoop : Prog isa := .loop doubleLoopBody .ne

end VG.Impl.Bignum.Arm
