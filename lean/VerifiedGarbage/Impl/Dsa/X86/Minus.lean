module
public import VerifiedGarbage.Impl.Mont.X86.Context


/-! # Forming p - 1 and q - 2 for DSA domain checks and Fermat powers -/

@[expose] public section
namespace VG.Impl.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def modulusMinus (n amount : Nat) : Prog isa :=
  .seq (setConstW (2 * n) (slot n 7) amount) (chainW .sbb (2 * n) (slot n 6) (slot n 0) (slot n 7))

end VG.Impl.Dsa.X86
