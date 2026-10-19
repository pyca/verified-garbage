module

public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Contract
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega

/-! # The key search's contract is its shared callable contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Spec.Ffdh

theorem stackArgs_seven (s : State) : List.map (stackArg s) (List.range 7) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5,
      stackArg s 6] := rfl

private theorem args_nowrap {s : State} (h : (s.gpr .rsp).toNat + 64 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 56 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.zero_add, Nat.mul_one]
  rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]
  simp only [BitVec.toNat_ofNat]
  omega

theorem key_implies_pre (s : State) (h : (keySearchContract abi 56).pre s) : keyContract.pre s := by
  sig_pre [keySearchContract, keySearchSig, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_seven,
    List.append_eq] at h
  sig_pre [keySearchContract, keySearchSig, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_seven,
    List.append_eq] at h
  sig_split h
  sig_reduce [keySearchContract, keySearchSig, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_seven,
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

theorem key_implies_post : ∀ s t, (keySearchContract abi 56).pre s →
    keyContract.post s t → (keySearchContract abi 56).post s t := by
  sig_implies_post [keySearchContract, keySearchSig, abi, argRegs, keyContract, keyPost, keyResult,
    keyRand, keyA, keyDom, keyLen, keyRetries, stackArgs_seven, List.append_eq, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem key_implies_pub (s t : State) (_hs : (keySearchContract abi 56).pre s)
    (_ht : (keySearchContract abi 56).pre t) (h : (keySearchContract abi 56).pub s t) :
    keyContract.pub s t := by
  sig_pub [keySearchContract, keySearchSig, abi, argRegs, stackArgs_seven, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, rdi, rsi, rdx, rcx, r8, r9, a0, a1, a2, a3, a4, a5, a6⟩ := h
  have hl1 : (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)).length =
      (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt t.mem (t.gpr .r9) (stackArg t 0).toNat)).length := by
    simp only [List.length_map, Spec.Rsa.bytesAt, List.length_range, a0]
  have hl2 : (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt s.mem (stackArg s 6) 4)).length =
      (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt t.mem (stackArg t 6) 4)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range]
  obtain ⟨hab, hst⟩ := List.append_inj hleak (by simp only [List.length_append, hl1, hl2])
  obtain ⟨hdom, hw⟩ := List.append_inj hab hl1
  refine ⟨hsp, rdi, rsi, rdx, rcx, r8, r9, fun j hj => ?_,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hdom,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, hst⟩
  match j, hj with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ => exact a5
  | 6, _ => exact a6
  | _ + 7, h => omega

/-- A valid 64-octet domain (p = 2^511 + 1, g = 2, no q), an empty tape and
disjoint buffers. -/
private def keySat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x5000 | .r9 => 0x3000
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6008 then 0x80 else if a = 0x6010 then 0x40 else if a = 0x6019 then 0x70
    else if a = 0x6029 then 0x80 else if a = 0x6030 then 0x20 else if a = 0x6031 then 0x04
    else if a = 0x6039 then 0x40 else if a = 0x4010 then 0x40 else if a = 0x3000 then 0x80
    else if a = 0x303F then 0x01 else if a = 0x307F then 0x02 else 0
  rd := [⟨0x3000, 128⟩, ⟨0x7000, 0⟩, ⟨0x6008, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x5000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 128⟩]

theorem key_implies : keyContract.Implies (keySearchContract abi 56) where
  pre := key_implies_pre
  post := key_implies_post
  pub := key_implies_pub
  sat := by
    refine ⟨keySat, ?_⟩
    sig_iff
    sig_reduce [keySearchContract, keySearchSig, abi, argRegs, stackBelow, keyContract, keyPre,
      stackArgs_seven, List.append_eq, pLenValid, domainLenValid]
    sig_and_intros
    all_goals first
      | exact Region.disjoint_of_sep (by decide +kernel)
      | decide +kernel

end VG.Proof.Ffdh.X86_64.KeyGeneration
