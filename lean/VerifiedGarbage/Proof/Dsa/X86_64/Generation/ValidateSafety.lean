module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PowerSafety

/-! # The final domain validator preserves stack and MXCSR control state -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Rsa.X86_64

theorem checkParameters_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) :
    generationSafe (Generate.checkParameters sq mul) := by
  unfold generationSafe at hs hm ⊢
  unfold Generate.checkParameters Checks.signingKey Checks.publicPrefix Core.reduce
    Arithmetic.reduce Arithmetic.reduceSetup Arithmetic.reduceByte Arithmetic.reduceStep
    Core.publicPow PublicPower.power PublicPower.powerCore
    PublicPower.encodedPower PublicPower.expLoop PublicPower.byte PublicPower.window
    PublicPower.applyWindow Arithmetic.encodePower Arithmetic.constants
    Crt.tabBuild Crt.tabBuildN R2Words.choice R2Words.fast R2Words.old
  repeat' first
    | rw [generation_instrs_seqs]
    | rw [Code.allInstrs]
    | rw [List.all_append]
    | rw [List.all_cons]
  simp only [hs, hm]
  rfl

theorem validate_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (pLen qLen : Nat) :
    generationSafe (validate sq mul pLen qLen) := by
  unfold validate
  repeat' first
    | exact checkParameters_safe sq mul hs hm
    | apply generationSafe.seq
  all_goals rfl

end VG.Proof.Dsa.X86_64.Generation
