module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.MontgomerySetup

/-! Montgomery one and minus one share the existing multiplication and subtraction. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

def parentDifference (n out input : Nat) : Prog isa :=
  chainW .sbb (2 * n) (slot n out) (slot n 0) (slot n input)

def montgomeryMinusOne (n : Nat) : Prog isa := parentDifference n 7 6

def montgomeryConstants (n bits : Nat) : Prog isa :=
  .seq (montgomerySetup n bits)
    (.seq (montgomery n 6 4 3) (montgomeryMinusOne n))

end VG.Impl.Dsa.X86.Generation
