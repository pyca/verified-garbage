module

import VerifiedGarbage.Impl.Mont.X86.Dynamic
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.TCB.X86.Isa

/-! Shared public-count squaring loops; the multiplication body is emitted once. -/

@[expose] public section
namespace VG.Impl.Mont.X86.Dynamic
open VG VG.X86

def squareStepWith (square : Prog isa) : Prog isa :=
  .seq square (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)])

def repeatSquaresWith (square : Prog isa) (count : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 count))]) (.loop (squareStepWith square) .ne)

end VG.Impl.Mont.X86.Dynamic
