module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSafety

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ControllerSafety
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateSafety
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateSafety
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Instruction safety of the complete parameter-generation entry point -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)


variable {checkName : String}

theorem seedAttempt_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (hp : ∀ bits, generationSafe (prime bits))
    (pLen qLen : Nat) : generationSafe (seedAttempt (checkName := checkName) H1 H256 sq mul prime pLen qLen) := by
  have finish : generationSafe (finishDomain (checkName := checkName) sq mul pLen qLen) :=
    (show generationSafe (pack pLen qLen) from rfl).seq (validate_safe (checkName := checkName) sq mul hs hm pLen qLen)
  exact ((show generationSafe (.block (seedArguments qLen)) from rfl).seq
    (subgroup_safe h1 h256 prime hp qLen)).seq
    (onSuccess_safe ((primeSearch_safe h1 h256 prime hp pLen qLen).seq
      (onSuccess_safe ((generatorSearch_safe sq mul hs hm pLen).seq (onSuccess_safe finish)))))

theorem generate_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (hp : ∀ bits, generationSafe (prime bits))
    (pLen qLen : Nat) : generationSafe (generate (checkName := checkName) H1 H256 sq mul prime pLen qLen) :=
  (tapeLoop_safe (seedAttempt_safe (checkName := checkName) h1 h256 sq mul prime hs hm hp pLen qLen) _ _).seq
    (show generationSafe finishOutput from rfl)

theorem dispatch_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (hp : ∀ bits, generationSafe (prime bits)) :
    generationSafe (dispatch (checkName := checkName) H1 H256 sq mul prime) := by
  have h128 := generate_safe (checkName := checkName) h1 h256 sq mul prime hs hm hp 128 20
  have h256' := generate_safe (checkName := checkName) h1 h256 sq mul prime hs hm hp 256 32
  have h384 := generate_safe (checkName := checkName) h1 h256 sq mul prime hs hm hp 384 32
  exact (show generationSafe (.block [.mov .rax (.mem (Impl.Mgf1.X86_64.sp 136)),
    .alu .cmp .rax (.imm 128)]) from rfl).seq
    (h128.ite ((show generationSafe (.block [.alu .cmp .rax (.imm 256)]) from rfl).seq
      (h256'.ite h384 .e)) .e)

theorem generationSafe.frame {body : Prog isa} (h : generationSafe body) (bytes : Nat) :
    generationSafe (.frame (.alloc bytes) body (.free bytes)) := by
  change ((true && _) && true) = true
  rw [h]; rfl

theorem entry_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (hp : ∀ bits, generationSafe (prime bits)) :
    generationSafe (code (checkName := checkName) H1 H256 sq mul prime) := by
  have body := (show generationSafe (.block (entryHeader ++ entryIncoming ++ entryDerived)) from rfl).seq
    (dispatch_safe (checkName := checkName) h1 h256 sq mul prime hs hm hp)
  exact ((show generationSafe (.block saveRegisters) from rfl).seq
    ((body.frame 296).seq (show generationSafe (.block restoreRegisters) from rfl))).frame 48

end VG.Proof.Dsa.X86_64.Generation
