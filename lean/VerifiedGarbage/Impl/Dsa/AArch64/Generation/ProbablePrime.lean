module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeSetup
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeLoop

/-! Trial division, to the first divisor, followed by the shared blinded Miller–Rabin loop. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate

/-- One word of the table of small primes: its four entries and the count, as
in `Candidate.trial`'s loop. -/
def trialWord : List (Prog isa) :=
  ([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++ trialEntry 2 ++
    trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa))

/-- `Candidate.trial`, stopping after the first word of the table one of whose
entries divides the candidate: the count `x10` is cleared when the mask `x1`
is set (`x8` is all ones). The candidates of DSA's parameter search are
public; RSA key generation's are not, and it keeps `Candidate.trial`. -/
def trialEarly : List (Prog isa) := [
  .block (ws ++ base aTab .x9 ++ tabWrite ++
    [movi .x3 128, movi .x4 256, movi .x5 17, .subs .x .x6 .x12 .x5, .csel .x .x10 .x4 .x3, movi .x1 0,
      movi .x7 0, .subImm .x .x8 .x7 1]),
  .loop (seqs (trialWord ++
    ([.block [.logic .eor .x .x3 .x1 .x8, .logic .and .x .x10 .x10 .x3]] : List (Prog isa))))
    (.nonzero .x .x10)]

def probablePrime (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) (len drawBytes : Nat) : Prog isa :=
  .seq (seqs trialEarly) (.ite (.zero .x .x1)
    (.seq (primeSetup mul) (millerRabin mul roundCode len drawBytes))
    (.block [movi .x3 3, sth .x3 kStat]))

end VG.Impl.Dsa.AArch64.Generation
