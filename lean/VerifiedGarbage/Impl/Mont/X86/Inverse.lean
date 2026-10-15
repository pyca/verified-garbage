module

public import VerifiedGarbage.Impl.Mont.X86

/-! # The runtime Montgomery inverse on 32-bit x86 -/

@[expose] public section

namespace VG.Impl.Mont.X86.Dynamic

open VG VG.X86 VG.Impl.Mont.X86

/-- Newton iteration, `ecx := ecx * (2 - ebx * ecx)`. -/
def newton : List Instr :=
  [.mov .eax (.reg .ebx), .mul .ecx, .mov .ebp (.imm 2),
   .alu .sub .ebp (.reg .eax), .mov .eax (.reg .ecx), .mul .ebp,
   .mov .ecx (.reg .eax)]

/-- Negative inverse of the odd word in `ebx`, returned in `eax`. Four
Newton steps suffice starting with the odd word, whose square is 1 modulo 8. -/
def inverse : List Instr :=
  [.mov .ecx (.reg .ebx)] ++ newton ++ newton ++ newton ++ newton ++
  [.mov .eax (.imm 0), .alu .sub .eax (.reg .ecx)]

/-- Initialize the inverse slot from the low word of a runtime modulus. -/
def setupInverse (mo inv : Nat) : List Instr :=
  [.mov .ebx (.mem (sc mo))] ++ inverse ++ [.store (sc inv) .eax]

end VG.Impl.Mont.X86.Dynamic
