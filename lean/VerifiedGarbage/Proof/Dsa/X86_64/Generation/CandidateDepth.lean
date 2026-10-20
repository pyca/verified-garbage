module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashDepth
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeDepth
import Mathlib.Tactic.Finiteness.Attr
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

theorem checkPrime_depth (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round)
    (w candidate len draw checks : Nat) : generationDepth (checkPrime mul round w candidate len draw checks) := by
  exact (show generationDepth (workspace w) by exact (show 0 ≤ 128 by decide)).seq
    ((show generationDepth (.block (headerArguments (primeArguments candidate len draw checks))) by exact (show 0 ≤ 128 by decide)).seq
      (primeBytes_depth mul round hm hr len draw))

theorem qCandidate_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256) :
    generationDepth (qCandidate H1 H256) := by
  exact (seedHash_depth h1 h256).seq ((show generationDepth (.block qArgs) by exact (show 0 ≤ 128 by decide)).seq
    (show generationDepth Impl.Ffdh.X86_64.ParameterCandidate.shape by exact (show 0 ≤ 128 by decide)))

theorem subgroup_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) (len : Nat) :
    generationDepth (subgroup H1 H256 mul round len) := by
  exact (qCandidate_depth h1 h256).seq ((show generationDepth (.block workspaceBase) by exact (show 0 ≤ 128 by decide)).seq
    ((checkPrime_depth mul round hm hr _ _ _ _ _).seq (show generationDepth (.block primeResult) by exact (show 0 ≤ 128 by decide))))

theorem pConstruct_depth {H : Stream} (h : HashDepth H) (pLen qLen : Nat) :
    generationDepth (pConstruct H pLen qLen) := by
  exact ((pHashes_depth h _ _).seq (show generationDepth (pShape qLen _ pLen) by exact (show 0 ≤ 128 by decide))).seq
    ((show generationDepth (.block workspaceBase) by exact (show 0 ≤ 128 by decide)).seq
      ((show generationDepth (workspace (pLen / 8)) by exact (show 0 ≤ 128 by decide)).seq
        (show generationDepth (candidateFromFrame pLen qLen) by exact (show 0 ≤ 128 by decide))))

theorem pTest_depth (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) (pLen : Nat) :
    generationDepth (pTest mul round pLen) := by
  unfold pTest
  apply generationDepth.seq (show generationDepth (.block candidateWidth) by exact (show 0 ≤ 128 by decide))
  apply generationDepth.ite (show generationDepth (.block (stackStatus 3)) by exact (show 0 ≤ 128 by decide))
  exact (checkPrime_depth mul round hm hr _ _ _ _ _).seq (show generationDepth (.block primeResult) by exact (show 0 ≤ 128 by decide))

theorem pAttempt_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) (pLen qLen : Nat) :
    generationDepth (pAttempt H1 H256 mul round pLen qLen) := by
  have hh : HashDepth (if qLen = 20 then H1 else H256) := by split <;> with_reducible assumption
  exact (show generationDepth (.block pAttemptArgs) by exact (show 0 ≤ 128 by decide)).seq
    (((pConstruct_depth hh pLen qLen).seq (pTest_depth mul round hm hr pLen)).seq
      (show generationDepth (.block searchReturn) by exact (show 0 ≤ 128 by decide)))

end VG.Proof.Dsa.X86_64.Generation
