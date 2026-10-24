module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeBytes
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # The probable-prime policy inherits instruction safety from shared arithmetic -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

theorem primeSetup_safe (mul : Nat → Nat → Nat → Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) : generationSafe (primeSetup mul) := by
  unfold generationSafe at hm ⊢
  simp only [primeSetup, primeR2, Impl.Dsa.X86_64.Arithmetic.constants,
    Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants,
    R2Words.choice, R2Words.fast, R2Words.old, VG.Impl.Bignum.X86_64.Public.R2Squares.run,
    VG.Impl.Bignum.X86_64.Public.R2Squares.init, VG.Impl.Bignum.X86_64.Public.R2Squares.next, seqs, Code.allInstrs, hm]
  rfl

theorem millerRabin_safe (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) (hr : generationSafe round) (len draw : Nat) :
    generationSafe (millerRabin mul round len draw) := by
  unfold generationSafe at hm hr ⊢
  simp only [millerRabin, primeIteration, drawRound, sampleRound,
    Impl.Ffdh.X86_64.ParameterCandidate.witnessRound, seqs, Code.allInstrs, hm, hr]
  rfl

theorem probablePrime_safe (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) (hr : generationSafe round) (len draw : Nat) :
    generationSafe (probablePrime mul round len draw) := by
  exact (show generationSafe (seqs Impl.RsaKeyGen.X86_64.Candidate.trial) by
    unfold generationSafe; decide +kernel).seq
    (((primeSetup_safe mul hm).seq (millerRabin_safe mul round hm hr len draw)).ite
      (show generationSafe (.block [.mov32 .rax (.imm 3), .store (hdr Impl.RsaKeyGen.X86_64.Candidate.kStat) .rax]) from rfl) _)

theorem primeBytes_safe (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) (hr : generationSafe round) (len draw : Nat) :
    generationSafe (primeBytes mul round len draw) :=
  (show generationSafe (loadPadded 0 20 18) from rfl).seq (probablePrime_safe mul round hm hr len draw)

end VG.Proof.Dsa.X86_64.Generation
