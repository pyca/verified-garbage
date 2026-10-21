module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Linear-time reduction by a public 64-bit exponent on i686

ECX and EBX hold the low and high words of a remainder below the exponent.
ESI holds the next candidate
bits, most significant first. Shift in one bit, subtract the exponent, and
select the subtraction under a mask combining the 64-bit carry and borrow.
The modulus's native words are read at fixed public workspace offsets.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Impl.Mont.X86

def shift : List Instr :=
  [.alu .add .esi (.reg .esi), .alu .adc .ecx (.reg .ecx), .alu .adc .ebx (.reg .ebx),
    .alu .sbb .ebp (.reg .ebp)]

def subtract (exponent : Nat) : List Instr :=
  [.mov .eax (.reg .ecx), .mov .edx (.reg .ebx),
    .alu .sub .eax (.mem (sc exponent)), .alu .sbb .edx (.mem (sc (exponent + 4))),
    .alu .adc .ebp (.imm 0), .alu .sub .ebp (.imm 1)]

def select : List Instr :=
  [.alu .xor .eax (.reg .ecx), .alu .and .eax (.reg .ebp), .alu .xor .ecx (.reg .eax),
    .alu .xor .edx (.reg .ebx), .alu .and .edx (.reg .ebp), .alu .xor .ebx (.reg .edx)]

def bit (exponent : Nat) : List Instr := shift ++ subtract exponent ++ select

end VG.Impl.RsaKeyGen.X86.Mod64
