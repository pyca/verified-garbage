module
public import VerifiedGarbage.Impl.Mont.X86.Words


/-! # Branch-free integer checks for DSA components -/

@[expose] public section
namespace VG.Impl.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

/-- `edx` all ones if `[a]` (`2 n` words) is nonzero, else zero. -/
def nonzero (n a : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0)]) <|
  .seq (wordLoop (2 * n) [.alu .or .ecx (.mem (at_ .ebp a))])
    (.block [.mov .edx (.reg .ecx), .mov .ecx (.imm 0), .alu .sub .ecx (.reg .edx),
      .alu .sbb .edx (.reg .edx)])

/-- `eax` all ones if `[a] < [m]` (`2 n` words), else zero. -/
def lessThan (n a m : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0)]) <|
  .seq (wordLoop (2 * n) ([.mov .eax (.mem (at_ .ebp a))] ++ restore ++
    [.alu .sbb .eax (.mem (at_ .ebp m)), .alu .sbb .ecx (.reg .ecx)]))
    (.block [.mov .eax (.reg .ecx)])

/-- Equality from two unsigned comparisons, returning its mask in edx. -/
def equal (n a b : Nat) : Prog isa :=
  .seq (lessThan n a b) <| .seq (.block [.mov .ebx (.reg .eax)]) <| .seq (lessThan n b a)
    (.block [.alu .or .eax (.reg .ebx), .alu .xor .eax (.imm (BitVec.allOnes 32)), .mov .edx (.reg .eax)])

/-- Accumulate a validity mask without control flow on its value. -/
def andFlag (flag : Nat) : List Instr :=
  [.mov .eax (.mem (sc flag)), .alu .and .eax (.reg .edx), .store (sc flag) .eax]

def checkRange (n a m flag : Nat) : Prog isa :=
  .seq (lessThan n a m) <| .seq (.block [.mov .ebx (.reg .eax)]) <| .seq (nonzero n a)
    (.block (.alu .and .edx (.reg .ebx) :: andFlag flag))

def checkZero (n a flag : Nat) (wantNonzero : Bool) : Prog isa :=
  .seq (nonzero n a)
    (.block ((if wantNonzero then [] else [.alu .xor .edx (.imm (BitVec.allOnes 32))]) ++ andFlag flag))

end VG.Impl.Dsa.X86
