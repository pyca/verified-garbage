module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSafety
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeSafety

/-! # Instruction safety of subgroup candidates and bounded prime search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem checkPrime_safe (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) (hr : generationSafe round)
    (w candidate len draw checks : Nat) : generationSafe (checkPrime mul round w candidate len draw checks) := by
  exact (show generationSafe (workspace w) from rfl).seq
    ((show generationSafe (.block (headerArguments (primeArguments candidate len draw checks))) from rfl).seq
      (primeBytes_safe mul round hm hr len draw))

theorem qCandidate_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256) :
    generationSafe (qCandidate H1 H256) := by
  exact (seedHash_safe h1 h256).seq ((show generationSafe (.block qArgs) from rfl).seq
    (show generationSafe Impl.Ffdh.X86_64.ParameterCandidate.shape from rfl))

theorem subgroup_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) (hr : generationSafe round) (len : Nat) :
    generationSafe (subgroup H1 H256 mul round len) := by
  exact (qCandidate_safe h1 h256).seq ((show generationSafe (.block workspaceBase) from rfl).seq
    ((checkPrime_safe mul round hm hr _ _ _ _ _).seq (show generationSafe (.block primeResult) from rfl)))

theorem pConstruct_safe {H : Stream} (h : HashSafety H) (pLen qLen : Nat) :
    generationSafe (pConstruct H pLen qLen) := by
  exact ((pHashes_safe h _ _).seq (show generationSafe (pShape qLen _ pLen) from rfl)).seq
    ((show generationSafe (.block workspaceBase) from rfl).seq
      ((show generationSafe (workspace (pLen / 8)) from rfl).seq
        (show generationSafe (candidateFromFrame pLen qLen) from rfl)))

theorem pTest_safe (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) (hr : generationSafe round) (pLen : Nat) :
    generationSafe (pTest mul round pLen) := by
  unfold pTest
  apply generationSafe.seq (show generationSafe (.block candidateWidth) from rfl)
  apply generationSafe.ite (show generationSafe (.block (stackStatus 3)) from rfl)
  exact (checkPrime_safe mul round hm hr _ _ _ _ _).seq (show generationSafe (.block primeResult) from rfl)

theorem pAttempt_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) (hr : generationSafe round) (pLen qLen : Nat) :
    generationSafe (pAttempt H1 H256 mul round pLen qLen) := by
  have hh : HashSafety (if qLen = 20 then H1 else H256) := by split <;> with_reducible assumption
  exact (show generationSafe (.block pAttemptArgs) from rfl).seq
    (((pConstruct_safe hh pLen qLen).seq (pTest_safe mul round hm hr pLen)).seq
      (show generationSafe (.block searchReturn) from rfl))

end VG.Proof.Dsa.X86_64.Generation
