module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateDepth
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PowerDepth

/-! # Search controllers inherit their bodies’ stack bounds -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem pSearch_depth {body : Prog isa} (hb : generationDepth body) (limit stride : Nat) :
    generationDepth (pSearch body limit stride) := by
  unfold generationDepth at hb ⊢
  simp only [pSearch, pSearchIteration, seqs, Code.x86_64Depth]
  simp only [Nat.max_le]
  and_intros
  all_goals first | exact hb | exact (show 0 ≤ 128 by decide)

theorem tapeLoop_depth {body : Prog isa} (hb : generationDepth body) (slots : TapeSlots) (width : Nat) :
    generationDepth (tapeLoop slots width body) := by
  unfold generationDepth at hb ⊢
  simp only [tapeLoop, tapeIteration, Code.x86_64Depth]
  simp only [Nat.max_le]
  and_intros
  all_goals first | exact hb | exact (show 0 ≤ 128 by decide)

theorem primeSearch_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) (pLen qLen : Nat) :
    generationDepth (primeSearch H1 H256 mul round pLen qLen) :=
  (show generationDepth (.block controlBase) by exact (show 0 ≤ 128 by decide)).seq
    (pSearch_depth (pAttempt_depth h1 h256 mul round hm hr pLen qLen) _ _)

theorem generatorSearch_depth (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (len : Nat) :
    generationDepth (generatorSearch sq mul len) :=
  tapeLoop_depth (generatorStep_depth sq mul hs hm len) _ _

theorem onSuccess_depth {body : Prog isa} (hb : generationDepth body) :
    generationDepth (onSuccess body) :=
  (show generationDepth (.block successStatus) by exact (show 0 ≤ 128 by decide)).seq (hb.ite (show generationDepth (.block []) by exact (show 0 ≤ 128 by decide)) _)

end VG.Proof.Dsa.X86_64.Generation
