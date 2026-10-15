module

public import VerifiedGarbage.Impl.Dsa.X86.Arithmetic
public import VerifiedGarbage.Impl.Dsa.X86.Bytes

/-! # Forming p - 1 and q - 2 for DSA domain checks and Fermat powers -/

@[expose] public section
namespace VG.Impl.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def modulusMinus (n amount : Nat) : List Instr :=
  VG.Impl.Weierstrass.X86.setConst n (slot n 7) amount ++
    chain (contextMod n) .sub .sbb (slot n 6) (slot n 0) (slot n 7)

end VG.Impl.Dsa.X86
