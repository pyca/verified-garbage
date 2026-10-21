module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Impl.Mont.X86

/-! # Lift a negative Montgomery inverse from 32 to 64 bits

EBX:ESI supplies the modulus's low and high native words, and ECX its
negative inverse modulo 2³². Three native products compute the high inverse
word in EAX. ECX remains the low inverse word. This is one Newton lift,
specialized to the already-zero low word of c*x+1.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.InverseLift
open VG VG.X86

def code : List Instr :=
  [.mov .eax (.reg .ebx), .mul .ecx, .alu .add .eax (.imm 1), .alu .adc .edx (.imm 0),
    .mov .ebp (.reg .edx), .mov .eax (.reg .esi), .mul .ecx, .alu .add .eax (.reg .ebp),
    .mov .ebp (.reg .eax), .mov .eax (.reg .ecx), .mul .ebp]

/-- Complete the high half after the ordinary 32-bit inverse setup. -/
def setup (mo inv : Nat) : List Instr :=
  [.mov .ebx (.mem (VG.Impl.Mont.X86.sc mo)),
    .mov .esi (.mem (VG.Impl.Mont.X86.sc (mo + 4))),
    .mov .ecx (.mem (VG.Impl.Mont.X86.sc inv))] ++ code ++
  [.store (VG.Impl.Mont.X86.sc (inv + 4)) .eax]

end VG.Impl.RsaKeyGen.X86.InverseLift
