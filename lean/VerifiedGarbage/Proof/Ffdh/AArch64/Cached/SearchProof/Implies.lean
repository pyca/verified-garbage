module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Contract
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Sat
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega

/-! # The key search's contract is its shared callable contract (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Spec.Ffdh

theorem stackArgs_seven (s : State) : List.map (stackArg s) (List.range 7) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,stackArg s 5,stackArg s 6] := rfl

private theorem args_nowrap {s : State} (h : s.sp.toNat + 56 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 56 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  exact h

theorem key_implies_pre (s : State) (h : (cachedKeySearchContract abi 64).pre s) : keyContract.pre s := by
  sig_pre [cachedKeySearchContract, cachedKeySearchSig,keySearchSig,Spec.Ffdh.generationContextAt, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads,inContext, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_seven,
    List.append_eq] at h
  sig_pre [cachedKeySearchContract, cachedKeySearchSig,keySearchSig,Spec.Ffdh.generationContextAt, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads,inContext, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_seven,
    List.append_eq] at h
  sig_split h
  sig_reduce [cachedKeySearchContract, cachedKeySearchSig,keySearchSig,Spec.Ffdh.generationContextAt, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads,inContext, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_seven,
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

theorem key_implies_post : ∀ s t, (cachedKeySearchContract abi 64).pre s →
    keyContract.post s t → (cachedKeySearchContract abi 64).post s t := by
  sig_implies_post [cachedKeySearchContract, cachedKeySearchSig,keySearchSig,Spec.Ffdh.generationContextAt, abi, argRegs, keyContract, keyPost, keyResult,
    keyRand, keyA, keyDom, keyLen, keyRetries, stackArgs_seven, List.append_eq, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem key_implies_pub (s t : State) (_hs : (cachedKeySearchContract abi 64).pre s)
    (_ht : (cachedKeySearchContract abi 64).pre t) (h : (cachedKeySearchContract abi 64).pub s t) :
    keyContract.pub s t := by
  sig_pub [cachedKeySearchContract, cachedKeySearchSig,keySearchSig,Spec.Ffdh.generationContextAt, abi, argRegs, stackArgs_seven, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4,a5,a6⟩ := h
  have hl1 : (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)).length =
      (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt t.mem (t.gpr .x5) (t.gpr .x6).toNat)).length := by
    simp only [List.length_map, Spec.Rsa.bytesAt, List.length_range, r6]
  have hl2 : (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt s.mem (stackArg s 4) 4)).length =
      (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt t.mem (stackArg t 4) 4)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range]
  obtain ⟨hab, hst⟩ := List.append_inj hleak (by simp only [List.length_append, hl1, hl2])
  obtain ⟨hdom, hw⟩ := List.append_inj hab hl1
  refine ⟨hsp, ?_, fun j hj => ?_,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hdom,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, hst⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  match j, hj with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ =>exact a5
  | 6, _ =>exact a6
  | _ + 7, h =>omega

theorem key_implies : keyContract.Implies (cachedKeySearchContract abi 64) where
  pre := key_implies_pre
  post := key_implies_post
  pub := key_implies_pub
  sat:=key_sat

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
