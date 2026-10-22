module

public import VerifiedGarbage.Impl.Mont.X86.Words

/-! # Wrapped seed addition from least to most significant byte

`esi` and `ebx` are disjoint source and destination pointers. `edx` holds
the public offset, below 2^31. The reviewed generation sizes use 20 or 32
bytes; no branch depends on a seed byte or on a carry.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def seedAddByte (i : Nat) : List Instr :=
  [.movzx8 .eax (at_ .esi i), .alu .add .edx (.reg .eax), .mov .eax (.reg .edx),
   .store8 (at_ .ebx i) .al, .shift .shr .edx 8]

def seedAdd : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block (seedAddByte n)) (seedAdd n)

end VG.Impl.Dsa.X86.Generation
