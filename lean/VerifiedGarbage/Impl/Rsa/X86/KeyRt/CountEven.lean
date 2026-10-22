module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt

/-! Record an array's parity and count a conditional halving. -/

@[expose] public section
namespace VG.Impl.Rsa.X86.KeyRt
open VG VG.X86 VG.Impl.Mont.X86

def countEven (L : Lay) (bit counter array : Nat) : List Instr :=
  bitOf L bit array ++
  [.mov .eax (.mem (sc bit)), .alu .xor .eax (.imm 1), .store (sc bit) .eax,
   .mov .edx (.mem (sc counter)), .alu .add .edx (.reg .eax), .store (sc counter) .edx]

end VG.Impl.Rsa.X86.KeyRt
