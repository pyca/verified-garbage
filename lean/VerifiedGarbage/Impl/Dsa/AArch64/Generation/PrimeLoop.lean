module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.DrawCopy
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SampleRound
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate

/-! Consume whole witness draws until the shared policy finishes or the tape ends. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate

def primeLoopInit : List Instr :=
  [movi .x3 1, sth .x3 kI, movi .x3 0, sth .x3 kUni]

def tapeCheck : List Instr :=
  [ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag

def primeIteration (body : Prog isa) : Prog isa := seqs [
  .block tapeCheck,
  .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) body,
  .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]

def drawRound (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) (len drawBytes : Nat) : Prog isa :=
  .seq (drawCopy len drawBytes) (sampleRound mul roundCode len)

def millerRabin (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) (len drawBytes : Nat) : Prog isa :=
  .seq (.block primeLoopInit)
    (.loop (primeIteration (drawRound mul roundCode len drawBytes)) (.zero .x .x3))

end VG.Impl.Dsa.AArch64.Generation
