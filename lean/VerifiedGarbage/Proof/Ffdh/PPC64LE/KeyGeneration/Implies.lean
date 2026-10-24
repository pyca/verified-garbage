module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Contract
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-! # The key search's contract is its shared callable contract (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE VG.Spec.Ffdh

theorem stackArgs_five (s : State) : List.map (stackArg s) (List.range 5) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

private theorem args_nowrap {s : State} (h : s.sp.toNat + 32 + 8 * 13 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 40 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem key_implies_pre (s : State) (h : (keySearchContract abi stackUse).pre s) : keyContract.pre s := by
  sig_pre [keySearchContract, keySearchSig, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_five,
    List.append_eq] at h
  sig_pre [keySearchContract, keySearchSig, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_five,
    List.append_eq] at h
  sig_split h
  sig_reduce [keySearchContract, keySearchSig, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_five,
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

theorem key_implies_post : ∀ s t, (keySearchContract abi stackUse).pre s →
    keyContract.post s t → (keySearchContract abi stackUse).post s t := by
  sig_implies_post [keySearchContract, keySearchSig, abi, argRegs, keyContract, keyPost, keyResult,
    keyRand, keyA, keyDom, keyLen, keyRetries, stackArgs_five, List.append_eq, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem key_implies_pub (s t : State) (_hs : (keySearchContract abi stackUse).pre s)
    (_ht : (keySearchContract abi stackUse).pre t) (h : (keySearchContract abi stackUse).pub s t) :
    keyContract.pub s t := by
  sig_pub [keySearchContract, keySearchSig, abi, argRegs, stackArgs_five, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, r3, r4, r5, r6, r7, r8, r9, r10, a0, a1, a2, a3, a4⟩ := h
  have hl1 : (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)).length =
      (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt t.mem (t.gpr .r8) (t.gpr .r9).toNat)).length := by
    simp only [List.length_map, Spec.Rsa.bytesAt, List.length_range, r9]
  have hl2 : (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt s.mem (stackArg s 4) 4)).length =
      (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt t.mem (stackArg t 4) 4)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range]
  obtain ⟨hab, hst⟩ := List.append_inj hleak (by simp only [List.length_append, hl1, hl2])
  obtain ⟨hdom, hw⟩ := List.append_inj hab hl1
  refine ⟨hsp, ?_, fun j hj => ?_,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hdom,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, hst⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩
  match j, hj with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | _ + 5, h => omega

/-- A valid 64-octet domain (p = 2^511 + 1, g = 2, no q), an empty tape and
disjoint buffers. -/
private def keySat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 64 | .r7 => 0x5000 | .r8 => 0x3000
    | .r9 => 128 | .r10 => 64 | _ => 0
  lr := 0
  sp := 0x6000
  mem a := if a = 0x6061 then 0x70 else if a = 0x6071 then 0x80 else if a = 0x6078 then 0x20
    else if a = 0x6079 then 0x04 else if a = 0x6081 then 0x40 else if a = 0x4010 then 0x40
    else if a = 0x3000 then 0x80 else if a = 0x303F then 0x01 else if a = 0x307F then 0x02 else 0
  rd := [⟨0x3000, 128⟩, ⟨0x7000, 0⟩, ⟨0x6060, 40⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x5000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 128⟩]

theorem key_implies : keyContract.Implies (keySearchContract abi stackUse) where
  pre := key_implies_pre
  post := key_implies_post
  pub := key_implies_pub
  sat := by
    refine ⟨keySat, ?_⟩
    sig_iff
    sig_reduce [keySearchContract, keySearchSig, abi, argRegs, stackBelow, keyContract, keyPre,
      stackArgs_five, List.append_eq, pLenValid, domainLenValid]
    sig_and_intros
    all_goals first
      | exact Region.disjoint_of_sep (by decide +kernel)
      | decide +kernel

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
