module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.CompactHeader
public import VerifiedGarbage.Impl.Mont.X86.Inverse64

/-! Lift the existing negative inverse into the shared compact header. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

/-- Ecx holds the existing 32-bit negative inverse; the candidate is array0. -/
def compactInverse : List Instr :=
  [.mov .eax (.mem (sc 256)), .mov .ebx (.mem (sc 260))] ++ extendInverse ++
  [.mov .edx (.reg .eax), .mov .eax (.reg .ecx)] ++ storeHeaderWord 56

end VG.Impl.Dsa.X86.Generation
