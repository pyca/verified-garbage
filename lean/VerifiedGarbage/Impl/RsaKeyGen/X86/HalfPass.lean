module

public import VerifiedGarbage.Impl.Mont.X86.Words

/-! # One masked native halving pass over the exponent

ECX holds zero or all ones. Each word is read before the previous word is
stored; a cleared extra source word supplies the incoming top bit.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.HalfPass
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def step (src out : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebp (src + 4))), .alu .and .eax (.imm 1), .shift .ror .eax 1,
    .mov .edx (.mem (at_ .ebp src)), .shift .shr .edx 1, .alu .add .edx (.reg .eax),
    .mov .ebx (.mem (at_ .ebp src)), .alu .xor .edx (.reg .ebx), .alu .and .edx (.reg .ecx),
    .alu .xor .ebx (.reg .edx), .store (at_ .ebp out) .ebx]

def code (n src out : Nat) : Prog isa := wordLoop n (step src out)

end VG.Impl.RsaKeyGen.X86.HalfPass
