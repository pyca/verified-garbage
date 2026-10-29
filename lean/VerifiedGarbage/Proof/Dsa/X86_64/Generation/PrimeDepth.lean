module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeDepth
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeBytes
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # The probable-prime policy inherits stack bounds from shared arithmetic -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

theorem primeSetup_depth (mul : Nat → Nat → Nat → Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) : generationDepth (primeSetup mul) := by
  unfold generationDepth at hm ⊢
  simp only [primeSetup, primeR2, Impl.Dsa.X86_64.Arithmetic.constants,
    Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants,
    R2Words.choice, R2Words.fast, R2Words.old, VG.Impl.Bignum.X86_64.Public.R2Squares.run,
    VG.Impl.Bignum.X86_64.Public.R2Squares.init, VG.Impl.Bignum.X86_64.Public.R2Squares.next, seqs, Code.x86_64Depth, Nat.max_le]
  and_intros
  all_goals first | exact hr | apply hm | exact (show 0 ≤ 128 by decide)

theorem millerRabin_depth (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) :
    generationDepth (millerRabin mul round) := by
  unfold generationDepth at hm hr ⊢
  simp only [millerRabin, primeIteration, drawRound, sampleRound,
    Impl.Ffdh.X86_64.ParameterCandidate.witnessRound, seqs, Code.x86_64Depth, Nat.max_le]
  and_intros
  all_goals first | exact hr | apply hm | exact (show 0 ≤ 128 by decide)

theorem probablePrime_depth (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) :
    generationDepth (probablePrime mul round) := by
  exact (show generationDepth (seqs Impl.RsaKeyGen.X86_64.Candidate.trial) by
    unfold generationDepth; decide +kernel).seq
    (((primeSetup_depth mul hm).seq (millerRabin_depth mul round hm hr)).ite
      (show generationDepth (.block [.mov32 .rax (.imm 3), .store (hdr Impl.RsaKeyGen.X86_64.Candidate.kStat) .rax]) by exact (show 0 ≤ 128 by decide)) _)

theorem primeBytes_depth (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) :
    generationDepth (primeBytes mul round) :=
  (show generationDepth (loadPadded 0 20 18) by exact (show 0 ≤ 128 by decide)).seq (probablePrime_depth mul round hm hr)

end VG.Proof.Dsa.X86_64.Generation
