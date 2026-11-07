module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Base
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Verified

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashVariants
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundCode
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateDepth
import Mathlib.Data.Nat.Basic
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashDepth
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSafety
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.RsaOaep.X86_64.Stack
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateDepth
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PowerDepth
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateSafety
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PowerSafety
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateSafety
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Call
import Mathlib.Algebra.Group.Nat.Defs
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryTape
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySave
/-! # Functional correctness for the existing hash and primality backends -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/HashCode.lean`, which only this module imported.
section

/-! # Existing hash variants supply the generator's instruction and stack checks -/

public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Pbkdf2.Md.X86_64

theorem generationSafe_of_noSp {c : Prog isa} (hs : NoSp c)
    (hm : c.allInstrs (fun i => !loadsMxcsr i) = true) : generationSafe c := by
  have sp := VG.Proof.RsaOaep.X86_64.SpSafe.of_noSp hs
  apply generationSafe_of_allInstrs
  rw [Code.allInstrs_eq]
  rw [Code.allInstrs_eq] at hm
  apply List.all_eq_true.mpr
  intro i hi
  rw [sp i hi, Bool.not_false, Bool.and_true]
  exact List.all_eq_true.mp hm i hi

theorem hashCode_safe (v : MdHash) : HashSafety v.H.stream :=
  ⟨generationSafe_of_noSp v.ok.initSp v.K.iMx,
    generationSafe_of_noSp v.ok.updSp v.ok.updMx,
    generationSafe_of_noSp v.ok.finSp v.ok.finMx⟩

theorem hashCode_depth (v : MdHash) : HashDepth v.H.stream where
  init := by
    change v.H.initC.x86_64Depth ≤ 120
    rw [x86_64Depth_noSp v.ok.initSp]
    have hd := v.ok.initDepth
    omega
  update := by
    change v.H.updC.x86_64Depth ≤ 120
    rw [x86_64Depth_noSp v.ok.updSp]
    have hd := v.ok.updDepth
    omega
  finish := by
    change v.H.finC.x86_64Depth ≤ 120
    rw [x86_64Depth_noSp v.ok.finSp]
    have hd := v.ok.finDepth
    omega

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ControllerDepth.lean`, which only this module imported.
section

/-! # Search controllers inherit their bodies’ stack bounds -/

public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem pSearch_depth {body : Prog isa} (hb : callerDepth body) (limit stride : Nat) :
    callerDepth (pSearch body limit stride) := by
  unfold callerDepth at hb ⊢
  simp only [pSearch, pSearchIteration, seqs, Code.x86_64Depth]
  simp only [Nat.max_le]
  and_intros
  all_goals first | exact hb | exact (show 0 ≤ 192 by decide)

theorem tapeLoop_depth {body : Prog isa} (hb : callerDepth body) (slots : TapeSlots) (width : Nat) :
    callerDepth (tapeLoop slots width body) := by
  unfold callerDepth at hb ⊢
  simp only [tapeLoop, tapeIteration, Code.x86_64Depth]
  simp only [Nat.max_le]
  and_intros
  all_goals first | exact hb | exact (show 0 ≤ 192 by decide)

theorem primeSearch_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (prime : Prog isa) (hp : callerDepth prime) (pLen qLen : Nat) :
    callerDepth (primeSearch H1 H256 prime pLen qLen) :=
  (callerDepth.of (generationDepth.block _)).seq
    (pSearch_depth (pAttempt_depth h1 h256 prime hp pLen qLen) _ _)

theorem generatorSearch_depth (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (len : Nat) :
    callerDepth (generatorSearch sq mul len) :=
  tapeLoop_depth (callerDepth.of (generatorStep_depth sq mul hs hm len)) _ _

theorem onSuccess_depth {body : Prog isa} (hb : callerDepth body) :
    callerDepth (onSuccess body) :=
  (callerDepth.of (generationDepth.block _)).seq (hb.ite (callerDepth.of (generationDepth.block _)) _)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ControllerSafety.lean`, which only this module imported.
section

/-! # Bounded seed, prime, and generator controllers inherit their bodies' safety -/

public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem pSearch_safe {body : Prog isa} (hb : generationSafe body) (limit stride : Nat) :
    generationSafe (pSearch body limit stride) := by
  unfold generationSafe at hb ⊢
  simp only [pSearch, pSearchIteration, seqs, generationOk, hb]
  rfl

theorem tapeLoop_safe {body : Prog isa} (hb : generationSafe body) (slots : TapeSlots) (width : Nat) :
    generationSafe (tapeLoop slots width body) := by
  unfold generationSafe at hb ⊢
  simp only [tapeLoop, tapeIteration, generationOk, hb]
  rfl

theorem primeSearch_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (prime : Prog isa) (hp : generationSafe prime) (pLen qLen : Nat) :
    generationSafe (primeSearch H1 H256 prime pLen qLen) :=
  (show generationSafe (.block controlBase) from rfl).seq
    (pSearch_safe (pAttempt_safe h1 h256 prime hp pLen qLen) _ _)

theorem generatorSearch_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (len : Nat) :
    generationSafe (generatorSearch sq mul len) :=
  tapeLoop_safe (generatorStep_safe sq mul hs hm len) _ _

theorem onSuccess_safe {body : Prog isa} (hb : generationSafe body) :
    generationSafe (onSuccess body) :=
  (show generationSafe (.block successStatus) from rfl).seq (hb.ite (show generationSafe (.block []) from rfl) _)

end VG.Proof.Dsa.X86_64.Generation
end

end
