module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Factor
public import VerifiedGarbage.Impl.Rsa.X86.Div
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Round

/-! # Save the odd exponent once and reload it for each witness

The full word width includes the zero padding for a 160-bit subgroup.
The saved exponent and factor count lie beyond Montgomery temporaries.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def prepareExponent (n : Nat) : Prog isa :=
  .seq (roundMinusOne n) (.seq (factor n)
    (VG.Impl.Rsa.X86.Div.copyWords (2 * n) (slot n 8) primeExponent))

def restoreExponentCount : List Instr :=
  [.mov .eax (.mem (sc primeTwos)), .alu .sub .eax (.imm 1), .store (sc roundCount) .eax]

def restoreExponent (n : Nat) : Prog isa :=
  .seq (VG.Impl.Rsa.X86.Div.copyWords (2 * n) primeExponent (slot n 8)) (.block restoreExponentCount)
end VG.Impl.Dsa.X86.Generation
