module

public import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Montgomery

/-! # Prepare the shared Miller–Rabin workspace, including padded q

The 160-bit subgroup modulus uses four limbs for the shared round. DSA's
existing constants setup supports zero high limbs; the remaining modulus
preparation is shared with FFDH and RSA.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.Bignum.X86_64 (seqs)

def primeR2 (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block prepareHead) (Arithmetic.constants mul)

def primeSetup (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (primeR2 mul) (.seq (prepareConstants mul) (seqs expSetup))

end VG.Impl.Dsa.X86_64.Generation
