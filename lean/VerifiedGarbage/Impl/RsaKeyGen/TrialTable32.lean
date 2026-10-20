module

public import VerifiedGarbage.Impl.RsaKeyGen.Primes

/-! # Small-prime sieve entries with their prepared 32-bit Montgomery inverses

A candidate can reuse each divisor's negative inverse rather than repeat
Newton iteration during every sieve pass. A table entry is two native
words: the small prime, then its negative inverse modulo 2^32.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.TrialTable32

/-- Newton's inverse update modulo 2^32. -/
def newton (s x : BitVec 32) : BitVec 32 := x * (2 - s * x)

/-- Four updates from an odd s suffice: its square starts correct modulo 8. -/
def inverse (s : BitVec 32) : BitVec 32 :=
  0 - newton s (newton s (newton s (newton s s)))

/-- The low 32-bit word is the divisor, and the high word its negative inverse. -/
def entry (i : Nat) : Nat :=
  tabEntry i + 2 ^ 32 * (inverse (BitVec.ofNat 32 (tabEntry i))).toNat

end VG.Impl.RsaKeyGen.TrialTable32
