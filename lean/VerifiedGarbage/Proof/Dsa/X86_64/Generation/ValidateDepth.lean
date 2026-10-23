module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeDepth
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit


/-! # Stack bound for the final domain validator -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Rsa.X86_64

theorem checkParameters_depth (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) :
    generationDepth (Generate.checkParameters sq mul) := by
  unfold generationDepth at hs hm ⊢
  unfold Generate.checkParameters Checks.signingKey Checks.publicPrefix Core.reduce
    Arithmetic.reduce Arithmetic.reduceSetup Arithmetic.reduceByte Arithmetic.reduceStep
    Core.publicPow PublicPower.power PublicPower.powerCore
    PublicPower.encodedPower PublicPower.expLoop PublicPower.byte PublicPower.window
    PublicPower.squares PublicPower.squaresInit PublicPower.squaresNext
    PublicPower.applyWindow Arithmetic.encodePower Arithmetic.constants
    Crt.tabBuild Crt.tabBuildN Crt.toEnt Crt.copyArr R2Words.choice R2Words.fast R2Words.old
  repeat' first
    | rw [generation_depth_seqs]
    | rw [Code.x86_64Depth]
    | rw [List.foldr_append]
    | rw [List.foldr_cons]
  simp only [List.foldr_nil, Nat.max_le]
  and_intros
  all_goals first | exact hs | apply hm | exact (show 0 ≤ 128 by decide)

theorem validate_depth (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (pLen qLen : Nat) :
    generationDepth (validate sq mul pLen qLen) := by
  exact ((generationDepth.block _).seq (checkParameters_depth sq mul hs hm)).seq
    ((generationDepth.block _).seq ((generationDepth.block _).ite (generationDepth.block _) .e))

end VG.Proof.Dsa.X86_64.Generation
