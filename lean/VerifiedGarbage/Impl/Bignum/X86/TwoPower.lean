module

public import VerifiedGarbage.TCB.X86.Isa

/-! Construct both halves of 2^(t mod 64) with five masked rotations. -/

@[expose] public section
namespace VG.Impl.Bignum.X86.TwoPower
open VG VG.X86

def bit (j : Nat) : List Instr :=
  [.mov .ebx (.reg .ecx)] ++ (if j = 0 then [] else [.shift .shr .ebx j]) ++
  [.alu .and .ebx (.imm 1)]

def step (j : Nat) : List Instr :=
  bit j ++ [.mov .edx (.imm 0), .alu .sub .edx (.reg .ebx),
   .mov .ebx (.reg .eax), .shift .ror .eax (32 - 2 ^ j), .alu .xor .eax (.reg .ebx),
   .alu .and .eax (.reg .edx), .alu .xor .eax (.reg .ebx)]

/-- Input is ecx, output is edx:eax; ebx and ecx are scratch. -/
def code : List Instr :=
  [.alu .and .ecx (.imm 63), .mov .eax (.imm 1)] ++
  step 0 ++ step 1 ++ step 2 ++ step 3 ++ step 4 ++
  [.mov .edx (.reg .ecx), .shift .shr .edx 5, .alu .and .edx (.imm 1),
   .mov .ebx (.imm 0), .alu .sub .ebx (.reg .edx), .mov .edx (.reg .eax),
   .alu .and .edx (.reg .ebx), .alu .xor .eax (.reg .edx)]

end VG.Impl.Bignum.X86.TwoPower
