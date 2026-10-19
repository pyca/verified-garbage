module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorStep
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.TapeLoop

/-! Search complete chunks of the original generator-input tape. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64

def generatorSearch (mul : Nat → Nat → Nat → Prog isa) (len : Nat) : Prog isa :=
  tapeLoop generatorTape len (generatorStep mul len)

end VG.Impl.Dsa.AArch64.Generation
