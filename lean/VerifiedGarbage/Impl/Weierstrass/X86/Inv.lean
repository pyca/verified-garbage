module

public import VerifiedGarbage.Impl.Weierstrass.X86

/-! # Batched divsteps on 32-bit x86 -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86.Inv
open VG.X86 VG.Impl.Mont.X86

/-- Update a pair `(left, right)` in `ebx, eax`, with odd/swap masks in
`ecx, edx`. The matrix pairs double the resulting left word; the low-word
pair halves the resulting right word. -/
def pairRegs : List Instr :=
  [.mov .ebp (.reg .ebx), .alu .xor .ebp (.reg .edx), .alu .sub .ebp (.reg .edx),
   .alu .and .ebp (.reg .ecx), .alu .add .eax (.reg .ebp),
   .mov .ebp (.reg .eax), .alu .and .ebp (.reg .edx), .alu .add .ebx (.reg .ebp)]

def pair (left right : Nat) (matrix : Bool) : List Instr :=
  [.mov .ebx (.mem (sc left)), .mov .eax (.mem (sc right))] ++ pairRegs ++
  (if matrix then [.alu .add .ebx (.reg .ebx)] else [.shift .shr .eax 1]) ++
  [.store (sc left) .ebx, .store (sc right) .eax]

/-- Seven words at `t`: delta, low f, low g, u, v, q, r.
Compute the odd/swap masks and update delta. -/
def maskRegs : List Instr :=
  [.mov .ebx (.reg .edx), .alu .and .eax (.imm 1),
   .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax),
   .shift .shr .edx 31, .alu .sub .edx (.imm 1),
   .alu .and .edx (.reg .ecx),
   .mov .eax (.reg .ebx), .alu .xor .eax (.reg .edx), .alu .sub .eax (.reg .edx),
   .alu .add .eax (.imm 2)]

def masks (t : Nat) : List Instr :=
  [.mov .eax (.mem (sc (t + 8))), .mov .edx (.mem (sc t))] ++ maskRegs ++ [.store (sc t) .eax]

def wordStep (t : Nat) : List Instr :=
  masks t ++ pair (t + 4) (t + 8) false ++
  pair (t + 12) (t + 20) true ++ pair (t + 16) (t + 24) true

def wordSteps (t n : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 n))])
    (.loop (.block (decCounter :: wordStep t ++ [testCounter])) .ne)

end VG.Impl.Weierstrass.X86.Inv
