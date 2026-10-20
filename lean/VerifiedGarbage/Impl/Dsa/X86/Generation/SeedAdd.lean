module
public import VerifiedGarbage.Impl.Mont.X86

/-! # Add a public search offset to a fixed-width big-endian seed

ESI points to the input, EDI to a disjoint output, and EAX holds the offset.
Carry propagates from the last byte toward the first; overflow is discarded.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def seedAddByte (i : Nat) : List Instr :=
  [.movzx8 .ecx (at_ .esi i), .alu .add .eax (.reg .ecx),
   .store8 (at_ .edi i) .al, .shift .shr .eax 8]

def seedAdd : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block (seedAddByte n)) (seedAdd n)
end VG.Impl.Dsa.X86.Generation
