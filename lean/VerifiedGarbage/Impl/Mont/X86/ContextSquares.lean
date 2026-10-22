module

public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Impl.Mont.X86.RepeatSquares

/-! A shared short Montgomery squaring loop for public-modulus setup. -/

@[expose] public section
namespace VG.Impl.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont.X86

/-- Square the setup residue and decrement its public iteration count. -/
def squareStep (n o : Nat) : Prog isa :=
  squareStepWith (mul (contextMod n) 0 (slot n 2) (slot n o) (slot n o) (slot n o))

/-- Repeated squaring at a fixed slot, with a public loop count. -/
def repeatSquares (n o count : Nat) : Prog isa :=
  repeatSquaresWith (mul (contextMod n) 0 (slot n 2) (slot n o) (slot n o) (slot n o)) count

def setupSquareStep (n : Nat) : Prog isa := squareStep n 4

/-- Six Montgomery squares turn `2^(65*n)` into `R²`: each doubles the
exponent above the radix `2^(64*n)`. The loop shares one multiplication body. -/
def setupSquares (n : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.imm 6)]) (.loop (setupSquareStep n) .ne)


end VG.Impl.Mont.X86.Dynamic
