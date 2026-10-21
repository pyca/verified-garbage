module

public import VerifiedGarbage.Impl.Rsa.X86.Inverse

/-! # Reusable native inverse bank for RSA generation

`inverseFrom` copies two `n`-word inputs from outside arrays 0–14 into
the inverse's bank. Choosing `n` independently of the modulus workspace
lets the public exponent use only two native words, and the CRT inverse
and LCM GCD use only the prime width. The source modulus must be odd and
at least three. The caller selects a fallback before entering this code.

The resulting gcd and coefficient are arrays 1 and 3. The coefficient
satisfies `x*a ≡ gcd(a,m) mod m` even when the inputs are not coprime.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Key
open VG VG.X86 VG.Impl.Rsa.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Mont.X86.Dynamic

def inverseBank (n : Nat) : Prog isa := seqs [
  copy n 1 aM,
  .block (setOne n 2),
  sub3 n aNM aZero aM]

def inverseLoad (n src mo : Nat) : Prog isa := seqs [
  zerosW hdr (15 * (n + 2)),
  Div.copyWords n src (slot n 0),
  Div.copyWords n mo (slot n aM)]

def inverseSetup (n src mo : Nat) : Prog isa :=
  .seq (inverseLoad n src mo) (inverseBank n)

def inverseFrom (n src mo : Nat) : Prog isa :=
  .seq (inverseSetup n src mo) (inverse n)

end VG.Impl.RsaKeyGen.X86.Key
