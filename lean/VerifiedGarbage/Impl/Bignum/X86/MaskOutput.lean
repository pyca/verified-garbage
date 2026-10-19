module

public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.Mont.X86.Words

/-! # Mask a checked RSA result without branching on input acceptance

ECX holds all ones for an accepted input and zero otherwise. Array five
is available after exponentiation and supplies the zero alternative.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

def maskOutput (n : Nat) : Prog isa :=
  .seq (zerosW (slot n 5) (2 * n)) (selectsW (2 * n) (slot n 5) (slot n 7) (slot n 7))

end VG.Impl.Bignum.X86.PublicContext
