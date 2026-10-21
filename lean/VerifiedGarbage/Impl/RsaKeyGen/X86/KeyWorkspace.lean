module

public import VerifiedGarbage.Impl.Rsa.X86.KeyWs
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Product

/-! # Workspace for native RSA assembly from two primes

The modulus has `n` native words; each prime has `n / 2`. Arrays 0–14
are reserved for the existing binary inverse implementation. Persistent
values start at array 15, so using the inverse at a smaller width cannot
overwrite them. The 18 cdecl arguments occupy header bytes 0–71.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Key
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Rsa.X86.Keys

def nArr : Nat := 32
def aOne : Nat := 15
def aPa : Nat := 16
def aQa : Nat := 17
def aPm : Nat := 18
def aQm : Nat := 19
def aPhi : Nat := 20
def aL : Nat := 21
def aD : Nat := 22
def aN : Nat := 23
def aQi : Nat := 24
def aDp : Nat := 25
def aDq : Nat := 26
def aE : Nat := 27
def aDen : Nat := 28
def aU : Nat := 29
def aV : Nat := 30
def aHalf : Nat := 31

def kEv : Nat := 80
def kEvHi : Nat := 84
def kOk : Nat := 88
def kFlag : Nat := 92
def kProduct : Nat := 128

/-- Clear every array, including the two extra carry words, and set one. -/
def clearArrays (n : Nat) : Prog isa :=
  .seq (zerosW hdr (nArr * (n + 2))) (.block (setOne n aOne))

/-- Product of two prime-width arrays into a modulus-width array. -/
def primeProduct (n out a b : Nat) : Prog isa :=
  Product.code (n / 2) (n / 2) (slot n out) (slot n a) (slot n b) kProduct

/-- Copy a smaller native integer into a cleared modulus-width array. -/
def widenCopy (n k out src : Nat) : Prog isa :=
  .seq (zerosW (slot n out) (n + 2))
    (VG.Impl.Rsa.X86.Div.copyWords k src (slot n out))

end VG.Impl.RsaKeyGen.X86.Key
