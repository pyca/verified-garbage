module

public import VerifiedGarbage.Impl.Dsa.X86.Bytes

/-! # Branch-free integer checks for DSA components -/

@[expose] public section
namespace VG.Impl.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86

def nonzero (n a : Nat) : List Instr :=
  ([.mov .edx (.mem (sc a))] : List Instr) ++
  ((List.range (2 * n - 1)).map fun j => .alu .or .edx (.mem (sc (a + 4 * (j + 1))))) ++
  ([.mov .ecx (.imm 0), .alu .sub .ecx (.reg .edx), .alu .sbb .edx (.reg .edx)] : List Instr)

def lessThan (n a m : Nat) : List Instr :=
  ((List.range (2 * n)).flatMap fun j =>
    [.mov .edx (.mem (sc (a + 4 * j))), .alu (if j = 0 then .sub else .sbb) .edx (.mem (sc (m + 4 * j)))]) ++
  ([.alu .sbb .eax (.reg .eax)] : List Instr)

/-- Equality from two unsigned comparisons, returning its mask in edx. -/
def equal (n a b : Nat) : List Instr :=
  lessThan n a b ++ ([.mov .ebx (.reg .eax)] : List Instr) ++ lessThan n b a ++
    [.alu .or .eax (.reg .ebx), .alu .xor .eax (.imm (BitVec.allOnes 32)), .mov .edx (.reg .eax)]

/-- Accumulate a validity mask without control flow on its value. -/
def andFlag (flag : Nat) : List Instr :=
  [.mov .eax (.mem (sc flag)), .alu .and .eax (.reg .edx), .store (sc flag) .eax]

def checkRange (n a m flag : Nat) : List Instr :=
  lessThan n a m ++ ([.mov .ebx (.reg .eax)] : List Instr) ++ nonzero n a ++
    ([.alu .and .edx (.reg .ebx)] : List Instr) ++ andFlag flag

def checkNonzero (n a flag : Nat) : List Instr :=
  nonzero n a ++ andFlag flag

def checkZero (n a flag : Nat) (wantNonzero : Bool) : List Instr :=
  nonzero n a ++ (if wantNonzero then [] else [.alu .xor .edx (.imm (BitVec.allOnes 32))]) ++ andFlag flag

end VG.Impl.Dsa.X86
