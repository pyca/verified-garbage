module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashDepth
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Stack bounds for subgroup candidates and prime search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem primeCall_depth (prime : Prog isa) (hp : callerDepth prime) (bits : Nat) :
    callerDepth (primeCall prime bits) := by
  unfold callerDepth at hp ⊢
  simp only [primeCall, primeCallResult, primeCallStatus, Code.x86_64Depth, Nat.max_le, Nat.zero_le,
    and_true, true_and]
  exact hp

theorem qCandidate_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256) (len : Nat) :
    generationDepth (qCandidate H1 H256 len) := by
  exact (seedHashAt_depth h1 h256 len).seq ((show generationDepth (.block qArgs) by exact (show 0 ≤ 128 by decide)).seq
    (show generationDepth Impl.Ffdh.X86_64.ParameterCandidate.shape by exact (show 0 ≤ 128 by decide)))

theorem subgroup_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (prime : Prog isa) (hp : callerDepth prime) (len : Nat) :
    callerDepth (subgroup H1 H256 prime len) :=
  (callerDepth.of (qCandidate_depth h1 h256 len)).seq (primeCall_depth prime hp _)

theorem pConstruct_depth {H : Stream} (h : HashDepth H) (pLen qLen : Nat) :
    generationDepth (pConstruct H pLen qLen) := by
  exact ((pHashes_depth h _ _).seq (show generationDepth (pShape qLen _ pLen) by exact (show 0 ≤ 128 by decide))).seq
    ((show generationDepth (.block workspaceBase) by exact (show 0 ≤ 128 by decide)).seq
      ((show generationDepth (workspace (pLen / 8)) by exact (show 0 ≤ 128 by decide)).seq
        (show generationDepth (candidateFromFrame pLen qLen) by exact (show 0 ≤ 128 by decide))))

theorem pTest_depth (prime : Prog isa) (hp : callerDepth prime) (pLen : Nat) :
    callerDepth (pTest prime pLen) := by
  unfold pTest
  exact (callerDepth.of (generationDepth.block _)).seq
    ((callerDepth.of (generationDepth.block _)).ite (primeCall_depth prime hp _) _)

theorem pAttempt_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (prime : Prog isa) (hp : callerDepth prime) (pLen qLen : Nat) :
    callerDepth (pAttempt H1 H256 prime pLen qLen) := by
  have hh : HashDepth (if qLen = 20 then H1 else H256) := by split <;> with_reducible assumption
  exact (callerDepth.of (generationDepth.block _)).seq
    (((callerDepth.of (pConstruct_depth hh pLen qLen)).seq (pTest_depth prime hp pLen)).seq
      (callerDepth.of (generationDepth.block _)))

end VG.Proof.Dsa.X86_64.Generation
