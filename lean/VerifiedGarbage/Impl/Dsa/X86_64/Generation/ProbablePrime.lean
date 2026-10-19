module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeSetup
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeLoop

/-! # DSA's full probable-prime operation in native code -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate

/-- The small-prime rejection path consumes no witness bytes. Otherwise
prepare the candidate and call RSA's blinded Miller–Rabin machinery. -/
def probablePrime (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) (len drawBytes : Nat) : Prog isa :=
  .seq (seqs trial) (.ite .e
    (.seq (primeSetup mul) (millerRabin mul round len drawBytes))
    (.block [.mov32 .rax (.imm 3), .store (hdr kStat) .rax]))

end VG.Impl.Dsa.X86_64.Generation
