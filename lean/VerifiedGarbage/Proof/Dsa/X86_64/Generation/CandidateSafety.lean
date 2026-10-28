module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSafety
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Instruction safety of subgroup candidates and bounded prime search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem primeCall_safe (prime : Prog isa) (hp : generationSafe prime) (bits : Nat) :
    generationSafe (primeCall prime bits) :=
  (show generationSafe (.block (primeCallArgs bits)) from rfl).seq
    (hp.seq (show generationSafe primeCallResult from rfl))

theorem qCandidate_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256) (len : Nat) :
    generationSafe (qCandidate H1 H256 len) := by
  exact (seedHashAt_safe h1 h256 len).seq ((show generationSafe (.block qArgs) from rfl).seq
    (show generationSafe Impl.Ffdh.X86_64.ParameterCandidate.shape from rfl))

theorem subgroup_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (prime : Prog isa) (hp : generationSafe prime) (len : Nat) :
    generationSafe (subgroup H1 H256 prime len) :=
  (qCandidate_safe h1 h256 len).seq (primeCall_safe prime hp _)

theorem pConstruct_safe {H : Stream} (h : HashSafety H) (pLen qLen : Nat) :
    generationSafe (pConstruct H pLen qLen) := by
  exact ((pHashes_safe h _ _).seq (show generationSafe (pShape qLen _ pLen) from rfl)).seq
    ((show generationSafe (.block workspaceBase) from rfl).seq
      ((show generationSafe (workspace (pLen / 8)) from rfl).seq
        (show generationSafe (candidateFromFrame pLen qLen) from rfl)))

theorem pTest_safe (prime : Prog isa) (hp : generationSafe prime) (pLen : Nat) :
    generationSafe (pTest prime pLen) := by
  unfold pTest
  apply generationSafe.seq (show generationSafe (.block candidateWidth) from rfl)
  exact generationSafe.ite (show generationSafe (.block (stackStatus 3)) from rfl) (primeCall_safe prime hp _) _

theorem pAttempt_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (prime : Prog isa) (hp : generationSafe prime) (pLen qLen : Nat) :
    generationSafe (pAttempt H1 H256 prime pLen qLen) := by
  have hh : HashSafety (if qLen = 20 then H1 else H256) := by split <;> with_reducible assumption
  exact (show generationSafe (.block pAttemptArgs) from rfl).seq
    (((pConstruct_safe hh pLen qLen).seq (pTest_safe prime hp pLen)).seq
      (show generationSafe (.block searchReturn) from rfl))

end VG.Proof.Dsa.X86_64.Generation
