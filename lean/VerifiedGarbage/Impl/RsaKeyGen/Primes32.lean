module

public import VerifiedGarbage.Impl.RsaKeyGen.Primes

/-! Two small primes per word, shared by the 32-bit targets. -/

@[expose] public section
namespace VG.Impl.RsaKeyGen

def tabWord32 (j : Nat) : Nat := tabEntry (2 * j) + tabEntry (2 * j + 1) * 2 ^ 16

end VG.Impl.RsaKeyGen
