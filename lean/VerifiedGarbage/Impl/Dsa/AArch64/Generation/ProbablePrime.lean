module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeSetup
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeLoop

/-! Trial division followed by the shared blinded Miller–Rabin loop. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate

def probablePrime (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) (len drawBytes : Nat) : Prog isa :=
  .seq (seqs trial) (.ite (.zero .x .x1)
    (.seq (primeSetup mul) (millerRabin mul roundCode len drawBytes))
    (.block [movi .x3 3, sth .x3 kStat]))

end VG.Impl.Dsa.AArch64.Generation
