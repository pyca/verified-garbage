module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Contract
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega

/-! # The parameter search's contract is its shared callable contract (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Spec.Ffdh

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

private theorem args_nowrap {s : State} (h : s.sp.toNat + 16 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 16 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  exact h

theorem search_implies_pre (s : State) (h : (parameterSearchContract abi 32).pre s) : searchContract.pre s := by
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

theorem search_implies_post : ∀ s t, (parameterSearchContract abi 32).pre s →
    searchContract.post s t → (parameterSearchContract abi 32).post s t := by
  sig_implies_post [parameterSearchContract, parameterSearchSig, abi, argRegs, searchContract, searchPost,
    searchResult, genRand, genLen, genBits, genGen, genAttempts, stackArgs_two, List.append_eq,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_implies_pub (s t : State) (_hs : (parameterSearchContract abi 32).pre s)
    (_ht : (parameterSearchContract abi 32).pre t) (h : (parameterSearchContract abi 32).pub s t) :
    searchContract.pub s t := by
  sig_pub [parameterSearchContract, parameterSearchSig, abi, argRegs, stackArgs_two, List.append_eq] at h
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

theorem search_implies : searchContract.Implies (parameterSearchContract abi 32) where
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

end VG.Proof.Ffdh.AArch64.Generation
