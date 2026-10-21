module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Select the first nonzero paired word without a secret-dependent branch -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.LowPair
open VG VG.X86

/-- EBX/ESI retain the first nonzero pair; EAX/ECX supply the next pair. -/
def choose : List Instr :=
  [.mov .edx (.reg .ebx), .alu .or .edx (.reg .esi), .alu .cmp .edx (.imm 1),
    .alu .sbb .edx (.reg .edx), .alu .and .eax (.reg .edx), .alu .and .ecx (.reg .edx),
    .alu .or .ebx (.reg .eax), .alu .or .esi (.reg .ecx)]

def step (src index : Nat) : List Instr :=
  [.mov .eax (.mem (VG.Impl.Mont.X86.sc (src + 8 * index))),
    .mov .ecx (.mem (VG.Impl.Mont.X86.sc (src + 8 * index + 4)))] ++ choose

def steps (src : Nat) : Nat → Nat → Prog isa
  | _, 0 => .block []
  | start, count + 1 => .seq (.block (step src start)) (steps src (start + 1) count)

def scan (src count : Nat) : Prog isa :=
  .seq (.block [.mov .ebx (.imm 0), .mov .esi (.imm 0)]) (steps src 0 count)

end VG.Impl.RsaKeyGen.X86.LowPair
