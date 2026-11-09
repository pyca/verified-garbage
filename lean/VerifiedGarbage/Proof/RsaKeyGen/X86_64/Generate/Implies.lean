module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Contract
public import VerifiedGarbage.Proof.Framework.Contract

-- separate module: its proofs build in parallel with those of `Correct` and `CT`, which `Verified` also imports

/-! # The controller's contract is its shared callable contract -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG VG.X86_64 VG.Spec.RsaKeyGen

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

private theorem args_nowrap {s : State} (h : (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 16 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.zero_add, Nat.mul_one]
  rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]
  simp only [BitVec.toNat_ofNat]
  omega

theorem gen_implies_pre (s : State) (h : (keySearchContract abi stackUse).pre s) : genContract.pre s := by
  sig_pre [keySearchContract, keySearchSig, abi, argRegs, stackBelow, genContract, genPre,
    inReads, inWrites, inKey, inUsed, inRand, inScr, inState, inArgs, stackArgs_two,
    List.append_eq] at h
  sig_pre [keySearchContract, keySearchSig, abi, argRegs, stackBelow, genContract, genPre,
    inReads, inWrites, inKey, inUsed, inRand, inScr, inState, inArgs, stackArgs_two,
    List.append_eq] at h
  sig_split h
  sig_reduce [keySearchContract, keySearchSig, abi, argRegs, stackBelow, genContract, genPre,
    inReads, inWrites, inKey, inUsed, inRand, inScr, inState, inArgs, stackArgs_two,
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

theorem gen_implies_post : ∀ s t, (keySearchContract abi stackUse).pre s →
    genContract.post s t → (keySearchContract abi stackUse).post s t := by
  sig_implies_post [keySearchContract, keySearchSig, abi, argRegs, genContract, genPost,
    genResult, genRand, genE, genLen, genProgress, stackArgs_two,
    List.append_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem gen_implies_pub (s t : State) (_hs : (keySearchContract abi stackUse).pre s)
    (_ht : (keySearchContract abi stackUse).pre t) (h : (keySearchContract abi stackUse).pub s t) :
    genContract.pub s t := by
  sig_pub [keySearchContract, keySearchSig, abi, argRegs, stackArgs_two, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, rdi, rsi, rdx, rcx, r8, r9, a0, a1⟩ := h
  have hl : (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt s.mem (stackArg s 1) 7)).length =
      (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt t.mem (stackArg t 1) 7)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range]
  obtain ⟨hab, htr⟩ := List.append_inj hleak (by simp only [List.length_append, hl, List.length_cons,
    List.length_nil])
  obtain ⟨hw, hc⟩ := List.append_inj hab hl
  simp only [List.cons.injEq, and_true] at hc
  refine ⟨hsp, rdi, rsi, rdx, rcx, r8, r9, fun j hj => ?_,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, hc.1, hc.2.1, hc.2.2, htr⟩
  match j, hj with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | _ + 2, h => omega

/-- Primes of 32 octets, an empty tape, disjoint buffers and the state's
words for the width. -/
private def genSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 288 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 0 | .r9 => 0x8000
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6008 then 0x20 else if a = 0x6009 then 0x04 else if a = 0x6011 then 0x40
    else if a = 0x4008 then 0x20 else if a = 0x4010 then 0x20 else if a = 0x4012 then 0x10 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x6008, 16⟩]
  wr := [⟨0x1000, 288⟩, ⟨0x2000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 56⟩]

theorem gen_implies : genContract.Implies (keySearchContract abi stackUse) where
  pre := gen_implies_pre
  post := gen_implies_post
  pub := gen_implies_pub
  sat := by
    refine ⟨genSat, ?_⟩
    sig_iff
    sig_reduce [keySearchContract, keySearchSig, abi, argRegs, stackBelow, genContract,
      genPre, stackArgs_two, List.append_eq, primeLenValid]
    sig_and_intros
    all_goals first
      | exact Region.disjoint_of_sep (by decide +kernel)
      | decide +kernel

end VG.Proof.RsaKeyGen.X86_64.Generate
