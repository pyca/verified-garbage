module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent

/-! # Native CRT parameters and the private-exponent retry test -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Key
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.Keys

/-- A zero predecessor uses one as the divisor; accepted keys never use
the fallback. Rebuild the zero temporary after the inverse bank. -/
def divisorOf (n input : Nat) : Prog isa := seqs [
  constArray n aT1 0, eqS n kFlag input aT1 aT2,
  sel n aDen input aOne kFlag]

/-- Invert at prime width, and retain the modulus-width inverse status. -/
def qinvPart (n : Nat) : Prog isa := seqs [
  oddModulus n aPa aDen,
  inverseFrom (n / 2) (slot n aQa) (slot n aDen),
  gcdIsOne (n / 2), .block (andS kOk kOk kFlag),
  widenCopy n (n / 2) aQi (slot (n / 2) 3)]

def crtPart (n : Nat) : Prog isa := seqs [
  divisorOf n aPm,
  divisionFrom n (slot n aD) (slot n aDen) (slot n aU) (slot n aDp),
  divisorOf n aQm,
  divisionFrom n (slot n aD) (slot n aDen) (slot n aU) (slot n aDq)]

def nPart (n : Nat) : Prog isa := primeProduct n aN aPa aQa

/-- Branch on `dOk && d ≤ 2^(16*n)`, the specification's retry condition.
The subtract's borrow is a bit in EBX, never a data-dependent address. -/
def smallMask (n : Nat) : Prog isa := seqs [
  constArray n aT1 (2 ^ (16 * n) + 1), sub3 n aT2 aD aT1,
  .block [.mov .eax (.mem (sc kOk)), .alu .and .eax (.reg .ebx), .alu .cmp .eax (.imm 0)]]

end VG.Impl.RsaKeyGen.X86.Key
