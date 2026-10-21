module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyPrimes
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyInverse
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision

/-! # Native LCM from the RSA factor predecessors

After common halving, swapping on the parity of `v` puts an odd value in
`v` unless both running values are zero. The odd inverse bank computes
the gcd at prime width. A denominator of one handles `v ≤ 1`, including
the all-zero input, before the full product is divided.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Key
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Rsa.X86 VG.Impl.Rsa.X86.Keys

def constArray (n j x : Nat) : Prog isa := setConstW (n + 2) (slot n j) x

/-- Combine the comparison borrow in EBX with the low input bit. -/
def oddFlag (n input : Nat) : List Instr :=
  [.mov .eax (.imm 1), .alu .sub .eax (.reg .ebx),
    .alu .and .eax (.mem (sc (slot n input))), .alu .and .eax (.imm 1), .store (sc kFlag) .eax]

/-- Select a safe odd modulus of at least three; `kFlag` records validity. -/
def oddModulus (n input out : Nat) : Prog isa := seqs [
  constArray n aT1 3, sub3 n aT2 input aT1, .block (oddFlag n input),
  sel n out aT1 input kFlag]

def evenFlag (n input : Nat) : List Instr :=
  [.mov .eax (.mem (sc (slot n input))), .alu .and .eax (.imm 1),
    .alu .xor .eax (.imm 1), .store (sc kFlag) .eax]

def oddSecond (n : Nat) : Prog isa := seqs [
  .block (evenFlag n aV),
  copy n aT1 aU, sel n aU aU aV kFlag, sel n aV aV aT1 kFlag]

def gcdFrom (n : Nat) : Prog isa := seqs [
  inverseFrom (n / 2) (slot n aU) (slot n aDen),
  widenCopy n (n / 2) aDen (slot (n / 2) 1),
  sel n aDen aOne aDen kFlag]

def gcdPart (n : Nat) : Prog isa := seqs [oddSecond n, oddModulus n aV aDen, gcdFrom n]

def lcmPart (n : Nat) : Prog isa := seqs [
  twos n, gcdPart n,
  divisionFrom n (slot n aPhi) (slot n aDen) (slot n aL) (slot n aT1)]

end VG.Impl.RsaKeyGen.X86.Key
