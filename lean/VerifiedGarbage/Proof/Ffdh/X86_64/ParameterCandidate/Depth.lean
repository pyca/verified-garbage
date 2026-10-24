module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: the shared call's stack bound -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

private theorem depth_seqs (l : List (Prog isa)) :
    (seqs l).x86_64Depth = l.foldr (fun c n => max c.x86_64Depth n) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.foldr_cons, List.foldr_nil, Nat.max_zero]
    | cons b l => simp only [seqs, Code.x86_64Depth, List.foldr_cons] at ih ⊢; rw [ih]

private def codeWith (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  VG.Impl.Ffdh.X86_64.ParameterCandidate.code mul (R2Words.choice mul) round

private theorem template_depth (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, (mul o a b).x86_64Depth = 0) (hr : round.x86_64Depth ≤ 128) :
    (codeWith mul round).x86_64Depth ≤ 128 := by
  unfold codeWith VG.Impl.Ffdh.X86_64.ParameterCandidate.code VG.Impl.Ffdh.X86_64.ParameterCandidate.body VG.Impl.Ffdh.X86_64.ParameterCandidate.testCandidate VG.Impl.Ffdh.X86_64.ParameterCandidate.candidateFilter VG.Impl.Ffdh.X86_64.ParameterCandidate.testQ VG.Impl.Ffdh.X86_64.ParameterCandidate.testP VG.Impl.Ffdh.X86_64.ParameterCandidate.modulusPolicy VG.Impl.Ffdh.X86_64.ParameterCandidate.rounds VG.Impl.Ffdh.X86_64.ParameterCandidate.roundBody VG.Impl.Ffdh.X86_64.ParameterCandidate.roundRun VG.Impl.Ffdh.X86_64.ParameterCandidate.witnessRound VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareModulus VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareR2 VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  repeat' first
    | rw [depth_seqs]
    | rw [Code.x86_64Depth]
    | rw [List.foldr_cons]
    | rw [List.foldr_nil]
  simp only [hm, Nat.max_zero, Nat.zero_max, Nat.max_le]
  and_intros
  all_goals first | exact hr | decide +kernel

theorem candidateCode_depth (v : RoundImpl) : (candidateCode v).x86_64Depth ≤ 128 := by
  apply template_depth _ _ v.arithDepth
  change max 0 (max (v.code.x86_64Depth + 8) 0) ≤ 128
  simp only [Nat.zero_max, Nat.max_zero]
  have hd : v.code.x86_64Depth ≤ 120 := v.depth
  exact Nat.add_le_add_right hd 8

end VG.Proof.Ffdh.X86_64.ParameterCandidate
