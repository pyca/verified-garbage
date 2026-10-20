module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.ProbablePrime

/-! Test a candidate directly from its saved big-endian byte buffer. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64

def primeBytes (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa))
    (len drawBytes : Nat) : Prog isa :=
  .seq (seqs (Keys.loadA 0 20 VG.Impl.RsaKeyGen.AArch64.Candidate.kUsedP)) (probablePrime mul roundCode len drawBytes)

end VG.Impl.Dsa.AArch64.Generation
