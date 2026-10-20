module

public import VerifiedGarbage.Impl.Bignum.Arm.SubRow
public import VerifiedGarbage.Impl.Bignum.Arm.RowFull

/-! # Modular subtraction with a masked modulus addition

r0 points to an extended accumulator, r10 and r12 to the operands,
r9 to the modulus and lr holds the native word count. The accumulator's
two high words start at zero. The low words receive (a-b) modulo m;
the high words are scratch. All inputs are separate from the output.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def subModHead : List Instr := [.mov .r7 (.reg .r0), .mov .r8 (.reg .lr), .mov .r11 (.imm 0)]
def subModAddArgs : List Instr :=
  [.mov .r1 (.reg .r11), .mov .r0 (.reg .r7), .mov .r12 (.reg .r9),
   .mov .lr (.reg .r8), .mov .r11 (.imm 0)]
def subModBuffers : Prog isa :=
  .seq (.block subModHead) (.seq subRow (.seq (.block subModAddArgs) rowFull))

end VG.Impl.Bignum.Arm
