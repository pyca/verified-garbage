module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyLcm
public import VerifiedGarbage.Impl.Bignum.X86.LoadBE

/-! # The native RSA private exponent

For an odd public exponent, divide `L = e*Q + R`, invert `R` in a two-word
bank, and form `d = Q*(e-x) + (R*(e-x)+1)/e`. Only the small correction
uses 128-bit division; the expensive inverse stays at 64 bits. All division
uses the fixed native bit schedule, never the processor's divide instruction.
Even exponents use a modulus-width inverse with a safe odd fallback.

The private exponent is array `aD`. `kOk` records whether its inverse
exists; the final key checks and small-exponent retry follow separately.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Key
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Rsa.X86 VG.Impl.Rsa.X86.Keys

def loadExponent (n : Nat) : Prog isa := seqs [
  .block [.mov .esi (.mem (sc 56)), .mov .ecx (.mem (sc 60))],
  VG.Impl.Bignum.X86.loadBE 1 kEv,
  widenCopy n 2 aE kEv]

def gcdIsOne (k : Nat) : Prog isa := seqs [
  constArray k aT2 1, eqS k kFlag 1 aT2 aT1]

def borrowMask : List Instr :=
  [.mov .eax (.imm 1), .alu .sub .eax (.reg .ebx),
    .alu .and .eax (.mem (sc kFlag)), .store (sc kOk) .eax]

def lAtLeastTwo (n : Nat) : Prog isa := seqs [
  constArray n aT1 2, sub3 n aT2 aL aT1, .block borrowMask]

/-- Subtract two pairs before writing either output word. -/
def subtractPair (out a b : Nat) : List Instr :=
  [.mov .eax (.mem (sc a)), .mov .edx (.mem (sc (a + 4))),
    .alu .sub .eax (.mem (sc b)), .alu .sbb .edx (.mem (sc (b + 4))),
    .store (sc out) .eax, .store (sc (out + 4)) .edx]

/-- The two-word complement `e - x` into a cleared persistent array. -/
def complement (n : Nat) : Prog isa :=
  .seq (zerosW (slot n aDen) (n + 2))
    (.block (subtractPair (slot n aDen) kEv (slot 2 3)))

/-- The correction has two words; its numerator has four. -/
def correctionNumerator (n : Nat) : Prog isa := seqs [
  Product.code 2 2 (slot 4 1) (slot n aV) (slot n aDen) kProduct,
  constArray 4 2 1,
  chainW .adc 4 (slot 4 0) (slot 4 1) (slot 4 2)]

def correction (n : Nat) : Prog isa := seqs [
  correctionNumerator n, widenCopy 4 2 2 kEv, divisionCompute 4,
  widenCopy n 2 aV (slot 4 0)]

/-- The full quotient times a two-word scalar, plus the correction.
The product's four extra words lie in temporary arrays 0 and 1. -/
def dProduct (n : Nat) : Prog isa :=
  .seq (Product.code n 2 (slot n 0) (slot n aU) (slot n aDen) kProduct)
    (chainW .adc n (slot n aD) (slot n 0) (slot n aV))

def dOddPrepare (n : Nat) : Prog isa := seqs [
  divisionFrom n (slot n aL) (slot n aE) (slot n aU) (slot n aV),
  inverseFrom 2 (slot n aV) kEv,
  gcdIsOne 2, lAtLeastTwo n]

def dOddFinish (n : Nat) : Prog isa := seqs [complement n, correction n, dProduct n]

def dOdd (n : Nat) : Prog isa := .seq (dOddPrepare n) (dOddFinish n)

def dEven (n : Nat) : Prog isa := seqs [
  oddModulus n aL aDen,
  .block [.mov .eax (.mem (sc kFlag)), .store (sc kOk) .eax],
  divisionFrom n (slot n aE) (slot n aDen) (slot n aU) (slot n aV),
  inverseFrom n (slot n aV) (slot n aDen),
  gcdIsOne n,
  .block (andS kOk kOk kFlag),
  copy n aD 3]

def dZero : Prog isa := .block [.mov .eax (.imm 0), .store (sc kOk) .eax]

def notSlot (out input : Nat) : List Instr :=
  [.mov .eax (.imm 1), .alu .sub .eax (.mem (sc input)), .store (sc out) .eax]

def dOne (n : Nat) : Prog isa := seqs [
  copy n aD aOne,
  eqS n kFlag aL aOne aT1,
  .block (notSlot kOk kFlag)]

/-- Compare the entire public exponent to a native constant. -/
def equalExponent (value : BitVec 32) : List Instr :=
  [.mov .eax (.mem (sc kEv)), .alu .xor .eax (.imm value),
    .alu .or .eax (.mem (sc kEvHi)), .alu .cmp .eax (.imm 0)]

/-- Test the parity of the public exponent. -/
def parityExponent : List Instr :=
  [.mov .eax (.mem (sc kEv)), .alu .and .eax (.imm 1), .alu .cmp .eax (.imm 0)]

def dSelect (n : Nat) : Prog isa :=
    .seq (.block (equalExponent 0)) (.ite .e dZero
      (.seq (.block (equalExponent 1)) (.ite .e (dOne n)
        (.seq (.block parityExponent) (.ite .e (dEven n) (dOdd n))))))

def dPart (n : Nat) : Prog isa := .seq (loadExponent n) (dSelect n)

end VG.Impl.RsaKeyGen.X86.Key
