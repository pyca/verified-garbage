module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Contract
public import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
public import VerifiedGarbage.Proof.Framework.Contract

-- separate module: its proofs build in parallel with those of `Correct` and `CT`, which `Verified` also imports

/-! # The search's contract is its shared callable contract -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Search


open VG VG.X86_64 VG.Spec.RsaKeyGen

theorem stackArgs_six (s : State) : List.map (stackArg s) (List.range 6) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5] := rfl

private theorem args_nowrap {s : State} (h : (s.gpr .rsp).toNat + 56 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 48 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.zero_add, Nat.mul_one]
  rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]
  simp only [BitVec.toNat_ofNat]
  omega

theorem search_implies_pre (s : State) (h : (primeSearchContract abi stackUse).pre s) :
    searchContract.pre s := by
  sig_pre [primeSearchContract, primeSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
    inReads, inWrites, inOut, inUsed, inE, inP, inRand, inScr, inState, inArgs, stackArgs_six,
    List.append_eq] at h
  sig_pre [primeSearchContract, primeSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
    inReads, inWrites, inOut, inUsed, inE, inP, inRand, inScr, inState, inArgs, stackArgs_six,
    List.append_eq] at h
  sig_split h
  sig_reduce [primeSearchContract, primeSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
    inReads, inWrites, inOut, inUsed, inE, inP, inRand, inScr, inState, inArgs, stackArgs_six,
    List.append_eq]
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

theorem search_implies_post : ∀ s t, (primeSearchContract abi stackUse).pre s →
    searchContract.post s t → (primeSearchContract abi stackUse).post s t := by
  sig_implies_post [primeSearchContract, primeSearchSig, abi, argRegs, searchContract, searchPost,
    searchResult, searchRand, searchE, searchP, searchLen, searchRemaining, stackArgs_six,
    List.append_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_implies_pub (s t : State) (_hs : (primeSearchContract abi stackUse).pre s)
    (_ht : (primeSearchContract abi stackUse).pre t) (h : (primeSearchContract abi stackUse).pub s t) :
    searchContract.pub s t := by
  sig_pub [primeSearchContract, primeSearchSig, abi, argRegs, stackArgs_six, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, rdi, rsi, rdx, rcx, r8, r9, a0, a1, a2, a3, a4, a5⟩ := h
  have hl1 : (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)).length =
      (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt t.mem (t.gpr .rcx) (t.gpr .r8).toNat)).length := by
    simp only [List.length_map, Spec.Rsa.bytesAt, List.length_range, r8]
  have hl2 : (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt s.mem (stackArg s 5) 4)).length =
      (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt t.mem (stackArg t 5) 4)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range]
  obtain ⟨habc, htr⟩ := List.append_inj hleak (by simp only [List.length_append, hl1, hl2, List.length_cons,
    List.length_nil])
  obtain ⟨hab, hc⟩ := List.append_inj habc (by simp only [List.length_append, hl1, hl2])
  obtain ⟨he, hw⟩ := List.append_inj hab hl1
  simp only [List.cons.injEq, and_true] at hc
  refine ⟨hsp, rdi, rsi, rdx, rcx, r8, r9, fun j hj => ?_,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, hc.1, hc.2.1,
    (by rw [show searchLen s = searchLen t from congrArg BitVec.toNat rsi]
        exact Entropy.requested_congr hc.1 hc.2.2), htr⟩
  match j, hj with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ => exact a5
  | _ + 6, h => omega

/-- A 32-octet prime, `e = 0` of one octet, no other prime, an empty tape,
disjoint buffers and the state's words for the width. -/
private def searchSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 32 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .r9 => 0x5000
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6011 then 0x70 else if a = 0x6021 then 0x80 else if a = 0x6028 then 0x20
    else if a = 0x6029 then 0x02 else if a = 0x6031 then 0x40 else if a = 0x4008 then 0x20
    else if a = 0x4010 then 0x20 else if a = 0x4012 then 0x10 else 0
  rd := [⟨0x3000, 1⟩, ⟨0x5000, 0⟩, ⟨0x7000, 0⟩, ⟨0x6008, 48⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 8⟩, ⟨0x8000, 544 * 8⟩, ⟨0x4000, 32⟩]

theorem search_implies : searchContract.Implies (primeSearchContract abi stackUse) where
  pre := search_implies_pre
  post := search_implies_post
  pub := search_implies_pub
  sat := by
    refine ⟨searchSat, ?_⟩
    sig_iff
    sig_reduce [primeSearchContract, primeSearchSig, abi, argRegs, stackBelow, searchContract,
      searchPre, stackArgs_six, List.append_eq, primeLenValid]
    sig_and_intros
    all_goals first
      | exact Region.disjoint_of_sep (by decide +kernel)
      | decide +kernel

end VG.Proof.RsaKeyGen.X86_64.Search
