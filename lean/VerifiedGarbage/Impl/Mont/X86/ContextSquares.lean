module

public import VerifiedGarbage.Impl.Mont.X86.Context

/-! A shared short Montgomery squaring loop for public-modulus setup. -/

@[expose] public section
namespace VG.Impl.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont.X86

/-- Square the setup residue and decrement its public iteration count. -/
def setupSquareStep (n : Nat) : Prog isa :=
  .seq (mul (contextMod n) 0 (slot n 2) (slot n 4) (slot n 4) (slot n 4))
    (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)])

/-- Six Montgomery squares turn `2^(65*n)` into `R²`: each doubles the
exponent above the radix `2^(64*n)`. The loop shares one multiplication body. -/
def setupSquares (n : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.imm 6)]) (.loop (setupSquareStep n) .ne)


end VG.Impl.Mont.X86.Dynamic
