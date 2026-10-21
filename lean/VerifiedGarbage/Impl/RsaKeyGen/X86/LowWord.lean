module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Candidate minus one, and restoration after the general exponent check

An RSA candidate's low word is odd. Subtracting one cannot borrow, and
adding it back cannot carry. Both operations therefore change one native
word while preserving every higher word.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.LowWord
open VG VG.X86 VG.Impl.Mont.X86

def decrement (out : Nat) : List Instr :=
  [.mov .eax (.mem (sc out)), .alu .sub .eax (.imm 1), .store (sc out) .eax]

def increment (out : Nat) : List Instr :=
  [.mov .eax (.mem (sc out)), .alu .add .eax (.imm 1), .store (sc out) .eax]

end VG.Impl.RsaKeyGen.X86.LowWord
