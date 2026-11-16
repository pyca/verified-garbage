module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PowerSafety
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # The final domain validator preserves stack and MXCSR control state -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Rsa.X86_64


variable {checkName : String}

theorem checkParameters_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) :
    generationSafe (Generate.checkParameters sq mul) := by
  unfold generationSafe at hs hm ⊢
  unfold Generate.checkParameters Checks.signingKey Checks.publicPrefix Core.reduce
    Arithmetic.reduce Arithmetic.reduceSetup Arithmetic.reduceByte Arithmetic.reduceStep
    Core.publicPow PublicPower.power PublicPower.powerCore
    PublicPower.encodedPower PublicPower.expLoop PublicPower.byte PublicPower.window
    PublicPower.squares PublicPower.squaresInit PublicPower.squaresNext
    PublicPower.applyWindow Arithmetic.encodePower Arithmetic.constants
    Crt.tabBuild Crt.tabBuildN R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  -- one pass: a `rw` for each node of the code read the whole goal again
  simp only [generationOk_seqs, generationOk, List.all_append, List.all_cons, hs, hm]
  rfl

theorem validate_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (pLen qLen : Nat) :
    generationSafe (validate (checkName := checkName) sq mul pLen qLen) := by
  unfold validate
  refine .seq (.seq ?_ ((checkParameters_safe sq mul hs hm).call checkName)) (.seq ?_ ?_)
  all_goals rfl

end VG.Proof.Dsa.X86_64.Generation
