module

public import VerifiedGarbage.Impl.Bignum.Arm.ImportOperand

/-! # Import a private-key operand whose pointer and length are saved in the outer frame -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def savedOperandArgs (pointerSlot countSlot : Nat) : List Instr :=
  [.ldrSp .r4 pointerSlot, .ldrSp .r6 countSlot]
def savedOperand (o pointerSlot countSlot : Nat) : Prog isa :=
  .seq (.block (savedOperandArgs pointerSlot countSlot)) (importOperand o)

end VG.Impl.Bignum.Arm
