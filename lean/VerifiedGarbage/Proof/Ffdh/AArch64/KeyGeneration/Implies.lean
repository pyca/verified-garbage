module

public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Contract
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega

/-! # The key search's contract is its shared callable contract (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.KeyGeneration

open VG VG.AArch64 VG.Spec.Ffdh

theorem stackArgs_five (s : State) : List.map (stackArg s) (List.range 5) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

private theorem args_nowrap {s : State} (h : s.sp.toNat + 40 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 40 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  exact h

theorem key_implies_pre (s : State) (h : (keySearchContract abi 48).pre s) : keyContract.pre s := by
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

theorem key_implies_post : ∀ s t, (keySearchContract abi 48).pre s →
    keyContract.post s t → (keySearchContract abi 48).post s t := by
  sig_implies_post [keySearchContract, keySearchSig, abi, argRegs, keyContract, keyPost, keyResult,
    keyRand, keyA, keyDom, keyLen, keyRetries, stackArgs_five, List.append_eq, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem key_implies_pub (s t : State) (_hs : (keySearchContract abi 48).pre s)
    (_ht : (keySearchContract abi 48).pre t) (h : (keySearchContract abi 48).pub s t) :
    keyContract.pub s t := by
  sig_pub [keySearchContract, keySearchSig, abi, argRegs, stackArgs_five, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4⟩ := h
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
  | _ + 5, h => omega

/-- A valid 64-octet domain (p = 2^511 + 1, g = 2, no q), an empty tape and
disjoint buffers. -/
private def keySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x5000 | .x5 => 0x3000
    | .x6 => 128 | .x7 => 64 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6001 then 0x70 else if a = 0x6011 then 0x80 else if a = 0x6018 then 0x20
    else if a = 0x6019 then 0x04 else if a = 0x6021 then 0x40 else if a = 0x4010 then 0x40
    else if a = 0x3000 then 0x80 else if a = 0x303F then 0x01 else if a = 0x307F then 0x02 else 0
  rd := [⟨0x3000, 128⟩, ⟨0x7000, 0⟩, ⟨0x6000, 40⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x5000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 128⟩]

theorem key_implies : keyContract.Implies (keySearchContract abi 48) where
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

end VG.Proof.Ffdh.AArch64.KeyGeneration
