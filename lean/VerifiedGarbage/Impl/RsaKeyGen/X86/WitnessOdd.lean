module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Temporarily set a witness's low bit for its comparison against the odd candidate -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessOdd
open VG VG.X86 VG.Impl.Mont.X86

def mark (src : Nat) : List Instr :=
  [.mov .esi (.mem (sc src)), .mov .eax (.reg .esi), .alu .or .eax (.imm 1), .store (sc src) .eax]

def restore (src : Nat) : List Instr := [.store (sc src) .esi]

end VG.Impl.RsaKeyGen.X86.WitnessOdd
