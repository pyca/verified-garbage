module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TapeLoop

/-! # Native complete generator search over the original h tape -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64

def generatorSearch (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (len : Nat) : Prog isa :=
  tapeLoop generatorTape len (generatorStep sq mul len)

end VG.Impl.Dsa.X86_64.Generation
