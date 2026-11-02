module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Impl.Ffdh.AArch64.ParameterCandidate
public import VerifiedGarbage.Impl.Ffdh.AArch64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Contract
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Correct
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Implies
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.CTCode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTCode
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Code

/-! # The verified parameter search (AArch64)

For any candidate with no frames (`search_verified_of`), and for the
candidate calling each shared Miller–Rabin round (`search_verified`), as
`Generic/MillerRabin/AArch64/Ffdh.lean` registers it.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.MillerRabin.AArch64 (RoundImpl)

theorem search_verified_of (c : Cand) :
    Verified target (Impl.Ffdh.AArch64.Generation.Search.code c.call)
      (Spec.Ffdh.parameterSearchContract abi stackUse) :=
  Verified.of_correct (search_correct c) (search_constantTime c) search_implies

theorem candidate_noFrames (v : RoundImpl) : (code v.mont.mm v.kernel.run).noFrames = true := by
  simp only [code, main, tests, test, phase, shapeP, residue, sieve, halveQ, montPrep, millerRabin, draw, round,
    pResult, qResult, Impl.Rsa.AArch64.Keys.loadA, Impl.RsaKeyGen.AArch64.Candidate.trialEntry,
    Impl.RsaKeyGen.AArch64.Candidate.halfPass, Impl.RsaKeyGen.AArch64.Candidate.subA,
    Impl.RsaKeyGen.AArch64.Candidate.expSetup, Impl.Rsa.AArch64.r2Steps, Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs,
    Impl.Bignum.AArch64.R2Div.choice,
    Impl.RsaKeyGen.AArch64.Candidate.lowWord, Impl.RsaKeyGen.AArch64.Candidate.halfCond,
    RoundImpl.kernel, MillerRabin.AArch64.Kernel.called, Impl.MillerRabin.AArch64.Caller.call,
    List.cons_append, List.nil_append, List.append_nil, ite_true, ite_false, Bool.false_eq_true,
    Impl.Bignum.AArch64.seqs, Code.noFrames, Bool.and_eq_true, v.mmNoFrames, true_and, and_true]
  and_intros
  all_goals first | exact v.noFrames | rfl

/-- `vg_ffdh_parameter_candidate` calling the shared round `v`, as the search
calls it. -/
def Cand.ofRound (v : RoundImpl) : Cand where
  name := "vg_ffdh_parameter_candidate" ++ v.suffix
  code := Impl.Ffdh.AArch64.ParameterCandidate.code v.mont.mm v.kernel.run
  noFrames := candidate_noFrames v
  correct := ParameterCandidate.code_correct v.mont v.kernel
  ct := ParameterCandidate.code_constantTime v.mont v.kernel

/-- The search calling it. -/
abbrev searchCode (v : RoundImpl) : Prog isa := Impl.Ffdh.AArch64.Generation.Search.code (Cand.ofRound v).call

theorem search_verified (v : RoundImpl) :
    Verified target (searchCode v) (Spec.Ffdh.parameterSearchContract abi stackUse) :=
  search_verified_of (Cand.ofRound v)
end VG.Proof.Ffdh.AArch64.Generation
