module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Impl.Mont.X86.Inverse
public import VerifiedGarbage.Impl.Mont.X86.Words
public import VerifiedGarbage.Impl.Rsa.X86.PrivChecked

/-! Radix-2^16 trial reduction for the shared small-prime table. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86

/-- Eax is the next digit, edi the accumulator, ebx the divisor, and esi
its negative inverse modulo 2^16. The reduced accumulator is returned in
eax. Ecx and edx are scratch registers. -/
def trialReduce : List Instr :=
  [.alu .add .eax (.reg .edi), .mov .ecx (.reg .eax), .mul .esi,
   .alu .and .eax (.imm 65535), .mul .ebx,
   .alu .add .eax (.reg .ecx), .shift .shr .eax 16]

/-- Reuse the Montgomery inverse implementation for each odd trial prime.
The reducer only needs its low 16 bits. -/
def trialInverse : List Instr :=
  Mont.X86.Dynamic.inverse ++ [.mov .esi (.reg .eax)]

/-- Consume one half of a little-endian candidate word through ebp. -/
def trialDigit (offset : Nat) (high : Bool) : List Instr :=
  [.mov .eax (.mem (Mont.X86.at_ .ebp offset))] ++
  (if high then [.shift .shr .eax 16] else [.alu .and .eax (.imm 65535)]) ++
  trialReduce ++ [.mov .edi (.reg .eax)]

/-- The two halves of one candidate word, least significant first. -/
def trialCandidateWord (offset : Nat) : Prog isa :=
  .seq (.block (trialDigit offset false)) (.block (trialDigit offset true))

/-- Advance the public candidate pointer; its end is in the parent frame. -/
def trialAdvance (endSlot : Nat) : List Instr :=
  [.alu .add .ebp (.imm 4), .mov .edx (.mem (Mont.X86.at_ .esp endSlot)),
   .alu .cmp .ebp (.reg .edx)]

/-- The scan uses one word body for every public candidate width. -/
def trialScan (endSlot : Nat) : Prog isa :=
  .seq (.block [.mov .edi (.imm 0)])
    (.loop (.seq (trialCandidateWord 0) (.block (trialAdvance endSlot))) .ne)

/-- Test whether the bounded residue is zero or the divisor, using the
existing branchless zero test. -/
def trialFlag : List Instr :=
  [.mov .ebp (.reg .edi)] ++ Rsa.X86.PrivChecked.zeroTest ++
  [.mov .edx (.reg .eax), .mov .ebp (.reg .edi), .alu .xor .ebp (.reg .ebx)] ++
  Rsa.X86.PrivChecked.zeroTest ++ [.alu .or .eax (.reg .edx)]

def trialTest (endSlot : Nat) : Prog isa :=
  .seq (trialScan endSlot) (.block trialFlag)

/-- A trial prime in ebx; candidate bounds are kept in the parent frame. -/
def trialPrime (startSlot endSlot : Nat) : Prog isa :=
  .seq (.block trialInverse)
    (.seq (.block [.mov .ebp (.mem (Mont.X86.at_ .esp startSlot))]) (trialTest endSlot))

end VG.Impl.Dsa.X86.Generation
