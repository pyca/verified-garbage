module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Sample
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.RoundTail

/-! Prepare the chosen witness, call the shared round, and apply RSA's policy. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public

def witnessRound (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) : Prog isa :=
  .seq (mul aXm aX aR2) (seqs roundCode)

def sampleRound (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) (len : Nat) : Prog isa :=
  .seq (sampleWitness len) (.seq (witnessRound mul roundCode) roundTail)

end VG.Impl.Dsa.AArch64.Generation
