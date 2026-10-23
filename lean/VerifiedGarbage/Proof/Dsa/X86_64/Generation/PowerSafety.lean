module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Public generator exponentiation preserves stack and MXCSR control state -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Rsa.X86_64

theorem generation_instrs_seqs (p : Instr → Bool) (l : List (Code Instr Cond)) :
    (seqs l).allInstrs p = l.all (fun c => c.allInstrs p) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [seqs, Code.allInstrs, List.all_cons] at ih ⊢; rw [ih]

theorem generatorPower_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) :
    generationSafe (generatorPower sq mul) := by
  unfold generationSafe at hs hm ⊢
  unfold generatorPower Core.publicPow PublicPower.power PublicPower.powerCore
    PublicPower.encodedPower PublicPower.expLoop PublicPower.byte PublicPower.window
    PublicPower.squares PublicPower.squaresInit PublicPower.squaresNext
    PublicPower.applyWindow Arithmetic.encodePower Arithmetic.constants
    Crt.tabBuild Crt.tabBuildN R2Words.choice R2Words.fast R2Words.old
  repeat' first
    | rw [generation_instrs_seqs]
    | rw [Code.allInstrs]
    | rw [List.all_append]
    | rw [List.all_cons]
  simp only [hs, hm]
  rfl

theorem generatorPowerFresh_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (len : Nat) :
    generationSafe (generatorPowerFresh sq mul len) :=
  (show generationSafe (generatorModulus len) from rfl).seq (generatorPower_safe sq mul hs hm)

theorem generatorStep_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (len : Nat) :
    generationSafe (generatorStep sq mul len) := by
  have test : generationSafe (.block [.alu .test .rax (.reg .rax)]) := rfl
  have retry : generationSafe (.block (stackStatus 3)) := rfl
  have success : generationSafe (.block (stackStatus 1)) := rfl
  have run := (show generationSafe (.block generatorInput) from rfl).seq
    (generatorPowerFresh_safe sq mul hs hm len)
  exact (show generationSafe (generatorRangeFromFrame len false) from rfl).seq
    (test.seq (retry.ite (run.seq
      ((show generationSafe (generatorRangeFromFrame len true) from rfl).seq
        (test.seq (retry.ite success .e)))) .e))

end VG.Proof.Dsa.X86_64.Generation
