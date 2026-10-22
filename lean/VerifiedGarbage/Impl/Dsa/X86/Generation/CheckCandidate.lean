module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.ProbablePrime
public import VerifiedGarbage.Impl.Dsa.X86.Core
public import VerifiedGarbage.Impl.Mont.X86.Dynamic

/-! Load a saved big-endian candidate before the common primality routine. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

def checkCandidate (name : String) (code : Prog isa) (n len offset : Nat) : Prog isa :=
  .seq (Dsa.X86.Core.load n len (slot n 0) (.local offset)) (probablePrime name code n len)

end VG.Impl.Dsa.X86.Generation
