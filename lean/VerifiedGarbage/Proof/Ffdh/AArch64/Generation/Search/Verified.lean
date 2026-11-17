module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Impl.Ffdh.AArch64.ParameterCandidate
public import VerifiedGarbage.Impl.Ffdh.AArch64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Data
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Correct
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.CTCode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTCode
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Code

/-! ### `Ffdh.AArch64.Generation.Search.Implies`, which only this module used -/

section

/-! # The parameter search's contract is its shared callable contract (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Spec.Ffdh

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

private theorem args_nowrap {s : State} (h : s.sp.toNat + 16 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 16 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  exact h

theorem search_implies_pre (s : State) (h : (sievedParameterSearchContract abi 32).pre s) : searchContract.pre s := by
  sig_pre [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
    inReads, inWrites, inOut, inUsed, inRand, inScr, inCtl, inArgs, stackArgs_two, List.append_eq] at h
  sig_pre [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
    inReads, inWrites, inOut, inUsed, inRand, inScr, inCtl, inArgs, stackArgs_two, List.append_eq] at h
  sig_split h
  sig_reduce [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
    inReads, inWrites, inOut, inUsed, inRand, inScr, inCtl, inArgs, stackArgs_two, List.append_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.pairwise_cons, List.Pairwise.nil, and_true, false_implies,
    implies_true]
  sig_and_intros
  sig_close
  all_goals first
    | (intro x hx; cases hx)
    | exact True.intro
    | with_reducible assumption
    | with_reducible rfl
    | omega
    | with_reducible exact Region.Disjoint.symm ‹_›
    | exact args_nowrap ‹_›

theorem search_implies_post : ∀ s t, (sievedParameterSearchContract abi 32).pre s →
    searchContract.post s t → (sievedParameterSearchContract abi 32).post s t := by
  sig_implies_post [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, searchContract, searchPost,
    searchResult, genRand, genLen, genBits, genGen, genAttempts, stackArgs_two, List.append_eq,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_implies_pub (s t : State) (_hs : (sievedParameterSearchContract abi 32).pre s)
    (_ht : (sievedParameterSearchContract abi 32).pre t) (h : (sievedParameterSearchContract abi 32).pub s t) :
    searchContract.pub s t := by
  sig_pub [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackArgs_two, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1⟩ := h
  have hl1 : (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)).length =
      (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt t.mem (t.gpr .x5) (t.gpr .x6).toNat)).length := by
    simp only [List.length_map, Spec.Rsa.bytesAt, List.length_range, r6]
  obtain ⟨hr, hw⟩ := List.append_inj hleak hl1
  exact ⟨hsp, hr, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, r0, r1, r2, r3, r4, r5, r6, r7,
    a0, a1⟩

/-- A 512-bit search with an empty tape and disjoint buffers. -/
private def searchSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 512 | .x4 => 2 | .x5 => 0x3000
    | .x7 => 0x8000 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6000 then 0x20 else if a = 0x6001 then 0x04 else if a = 0x6009 then 0x40
    else if a = 0x4008 then 0x40 else if a = 0x4010 then 0x40 else if a = 0x4012 then 0x20 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x6000, 16⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 128⟩]

theorem search_implies : searchContract.Implies (sievedParameterSearchContract abi 32) where
  pre := search_implies_pre
  post := search_implies_post
  pub := search_implies_pub
  sat := by
    refine ⟨searchSat, ?_⟩
    sig_iff
    sig_reduce [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
      stackArgs_two, List.append_eq, parameterAttempts, parameterEntropy]
    sig_and_intros
    all_goals first
      | exact Region.disjoint_of_sep (by decide +kernel)
      | decide +kernel

end VG.Proof.Ffdh.AArch64.Generation

end

end


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
      (Spec.Ffdh.sievedParameterSearchContract abi stackUse) :=
  Verified.of_correct (search_correct c) (search_constantTime c) search_implies

theorem candidate_noFrames (v : RoundImpl) : (code v.mont.mm v.kernel.run).noFrames = true := by
  simp only [code, main, mainQ, mainP, tests, testQ, testRest, test, firstCheck, restChecks, phase, shapeP, residue, sieve, halveQ,
    montPrep, millerRabin, draw, round, pResult, qResult, Impl.Rsa.AArch64.Keys.loadA, Impl.RsaKeyGen.AArch64.Candidate.trialEntry,
    Impl.RsaKeyGen.AArch64.Candidate.halfPass, Impl.RsaKeyGen.AArch64.Candidate.subA,
    Impl.RsaKeyGen.AArch64.Candidate.expSetup, Impl.Rsa.AArch64.r2Steps, Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs,
    Impl.Bignum.AArch64.R2Div.choice,
    Impl.RsaKeyGen.AArch64.Candidate.lowWord, Impl.RsaKeyGen.AArch64.Candidate.halfCond,
    RoundImpl.kernel, MillerRabin.AArch64.Kernel.called, Impl.MillerRabin.AArch64.Caller.call,
    List.cons_append, List.nil_append, List.append_nil, ite_true, ite_false, Bool.false_eq_true,
    Impl.Bignum.AArch64.seqs, Code.noFrames, Bool.and_eq_true, v.mmNoFrames, true_and, and_true]
  and_intros
  all_goals first | rfl | exact v.noFrames

/-- `vg_ffdh_parameter_candidate_sieved` calling the shared round `v`, as the
search calls it. -/
def Cand.ofRound (v : RoundImpl) : Cand where
  name := "vg_ffdh_parameter_candidate_sieved" ++ v.suffix
  code := Impl.Ffdh.AArch64.ParameterCandidate.code v.mont.mm v.kernel.run
  noFrames := candidate_noFrames v
  correct := ParameterCandidate.code_correct v.mont v.kernel
  ct := ParameterCandidate.code_constantTime v.mont v.kernel

/-- The search calling it. -/
abbrev searchCode (v : RoundImpl) : Prog isa := Impl.Ffdh.AArch64.Generation.Search.code (Cand.ofRound v).call

theorem search_verified (v : RoundImpl) :
    Verified target (searchCode v) (Spec.Ffdh.sievedParameterSearchContract abi stackUse) :=
  search_verified_of (Cand.ofRound v)
end VG.Proof.Ffdh.AArch64.Generation
