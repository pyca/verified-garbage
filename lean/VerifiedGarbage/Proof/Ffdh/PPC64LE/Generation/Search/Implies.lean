module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Contract
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
meta import VerifiedGarbage.Proof.Framework.Contract

/-! # The parameter search's contract is its shared callable contract (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Spec.Ffdh

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

private theorem args_nowrap {s : State} (h : s.sp.toNat + 32 + 8 * 10 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 16 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem search_implies_pre (s : State) (h : (parameterSearchContract abi stackUse).pre s) :
    searchContract.pre s := by
  sig_pre [parameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
    inReads, inWrites, inOut, inUsed, inRand, inScr, inCtl, inArgs, stackArgs_two, List.append_eq] at h
  sig_pre [parameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
    inReads, inWrites, inOut, inUsed, inRand, inScr, inCtl, inArgs, stackArgs_two, List.append_eq] at h
  sig_split h
  sig_reduce [parameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
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

theorem search_implies_post : ∀ s t, (parameterSearchContract abi stackUse).pre s →
    searchContract.post s t → (parameterSearchContract abi stackUse).post s t := by
  sig_implies_post [parameterSearchContract, parameterSearchSig, abi, argRegs, searchContract, searchPost,
    searchResult, genRand, genLen, genBits, genGen, genAttempts, stackArgs_two, List.append_eq,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_implies_pub (s t : State) (_hs : (parameterSearchContract abi stackUse).pre s)
    (_ht : (parameterSearchContract abi stackUse).pre t) (h : (parameterSearchContract abi stackUse).pub s t) :
    searchContract.pub s t := by
  sig_pub [parameterSearchContract, parameterSearchSig, abi, argRegs, stackArgs_two, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, r3, r4, r5, r6, r7, r8, r9, r10, a0, a1⟩ := h
  have hl1 : (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)).length =
      (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt t.mem (t.gpr .r8) (t.gpr .r9).toNat)).length := by
    simp only [List.length_map, Spec.Rsa.bytesAt, List.length_range, r9]
  obtain ⟨hr, hw⟩ := List.append_inj hleak hl1
  exact ⟨hsp, hr, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, r3, r4, r5, r6, r7, r8, r9, r10,
    a0, a1⟩

/-- A 512-bit search with an empty tape and disjoint buffers. -/
private def searchSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 512 | .r7 => 2 | .r8 => 0x3000
    | .r10 => 0x8000 | _ => 0
  lr := 0
  sp := 0x6000
  mem a := if a = 0x6060 then 0x20 else if a = 0x6061 then 0x04 else if a = 0x6069 then 0x40
    else if a = 0x4008 then 0x40 else if a = 0x4010 then 0x40 else if a = 0x4012 then 0x20 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x6060, 16⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 128⟩]

theorem search_implies : searchContract.Implies (parameterSearchContract abi stackUse) where
  pre := search_implies_pre
  post := search_implies_post
  pub := search_implies_pub
  sat := by
    refine ⟨searchSat, ?_⟩
    sig_iff
    sig_reduce [parameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
      stackArgs_two, List.append_eq, parameterAttempts, parameterEntropy]
    sig_and_intros
    all_goals first
      | exact Region.disjoint_of_sep (by decide +kernel)
      | decide +kernel

end VG.Proof.Ffdh.PPC64LE.Generation
