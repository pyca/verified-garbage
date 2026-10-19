module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.ForceWitness
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.WitnessRange

/-! Uniform or forced witness selection at the candidate's actual byte width. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate

def loadWitness : Prog isa := seqs (loadA aX kOut kUsedP)

def forceStoredWitness (len : Nat) : Prog isa :=
  .block ([ldh .x1 kOut] ++ forceWitness len)

def testWitness : Prog isa := .seq loadWitness testRange

def sampleWitness (len : Nat) : Prog isa :=
  .seq testWitness (.ite (.zero .x .x9)
    (.seq (forceStoredWitness len) loadWitness) (.block []))

end VG.Impl.Dsa.AArch64.Generation
