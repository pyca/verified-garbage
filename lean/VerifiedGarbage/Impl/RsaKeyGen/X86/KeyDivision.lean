module

public import VerifiedGarbage.Impl.Rsa.X86.Div
public import VerifiedGarbage.Impl.Rsa.X86.KeyWs

/-! # Native division between persistent RSA key arrays

The four temporary arrays have modulus width. Inputs are copied before
outputs are written, so a persistent output may replace either input.
The divisor must be positive and its extra word is cleared explicitly.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Key
open VG VG.X86 VG.Impl.Rsa.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Mont.X86

def divisionLoad (n src divisor : Nat) : Prog isa := seqs [
  .block [.mov .eax (.imm 0), .store (sc (slot n 2 + 4 * n)) .eax],
  Div.copyWords n src (slot n 0),
  Div.copyWords n divisor (slot n 2)]

def divisionCompute (n : Nat) : Prog isa :=
  Div.code n (slot n 0) (slot n 1) (slot n 2) (slot n 3)

def divisionStore (n quotient remainder : Nat) : Prog isa :=
  .seq (Div.copyWords n (slot n 0) quotient) (Div.copyWords n (slot n 1) remainder)

def divisionFrom (n src divisor quotient remainder : Nat) : Prog isa :=
  .seq (divisionLoad n src divisor) (.seq (divisionCompute n) (divisionStore n quotient remainder))

end VG.Impl.RsaKeyGen.X86.Key
