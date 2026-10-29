module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeDepth
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Stack bound for public generator exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Rsa.X86_64

theorem generatorPower_depth (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) :
    generationDepth (generatorPower sq mul) := by
  unfold generationDepth at hs hm ⊢
  unfold generatorPower Core.publicPow PublicPower.power PublicPower.powerCore
    PublicPower.encodedPower PublicPower.expLoop PublicPower.byte PublicPower.window
    PublicPower.squares PublicPower.squaresInit PublicPower.squaresNext
    PublicPower.applyWindow Arithmetic.encodePower Arithmetic.constants
    Crt.tabBuild Crt.tabBuildN Crt.toEnt Crt.copyArr R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  repeat' first
    | rw [generation_depth_seqs]
    | rw [Code.x86_64Depth]
    | rw [List.foldr_append]
    | rw [List.foldr_cons]
  simp only [List.foldr_nil, Nat.max_le]
  and_intros
  all_goals first | exact hs | apply hm | exact (show 0 ≤ 128 by decide)

theorem generatorPowerFresh_depth (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (len : Nat) :
    generationDepth (generatorPowerFresh sq mul len) :=
  (show generationDepth (generatorModulus len) by exact (show 0 ≤ 128 by decide)).seq (generatorPower_depth sq mul hs hm)

theorem generatorStep_depth (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (len : Nat) :
    generationDepth (generatorStep sq mul len) := by
  have test : generationDepth (.block [.alu .test .rax (.reg .rax)]) := by exact (show 0 ≤ 128 by decide)
  have retry : generationDepth (.block (stackStatus 3)) := by exact (show 0 ≤ 128 by decide)
  have success : generationDepth (.block (stackStatus 1)) := by exact (show 0 ≤ 128 by decide)
  have run := (show generationDepth (.block generatorInput) by exact (show 0 ≤ 128 by decide)).seq
    (generatorPowerFresh_depth sq mul hs hm len)
  exact (show generationDepth (generatorRangeFromFrame len false) by exact (show 0 ≤ 128 by decide)).seq
    (test.seq (retry.ite (run.seq
      ((show generationDepth (generatorRangeFromFrame len true) by exact (show 0 ≤ 128 by decide)).seq
        (test.seq (retry.ite success .e)))) .e))

end VG.Proof.Dsa.X86_64.Generation
