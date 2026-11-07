module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Generate.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract

-- separate module: its proofs build in parallel with those of `Correct` and `CT`, which `Verified` also imports

/-! # The controller's contract is its shared callable contract (ARMv7) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Spec.RsaKeyGen

theorem gen_implies_pre (s : State) (h : (keySearchContract abi stackUse).pre s) : genContract.pre s := by
  sig_pre [keySearchContract, keySearchSig, abi, argRegs, reduceClassify, Loc.val, stackBelow,
    genContract, genPre, inReads, inWrites, inKey, inUsed, inRand, inScr, inState, inArgs, inStack,
    State.addr, List.append_eq] at h
  sig_split h
  sig_reduce [keySearchContract, keySearchSig, abi, argRegs, reduceClassify, Loc.val, stackBelow,
    genContract, genPre, inReads, inWrites, inKey, inUsed, inRand, inScr, inState, inArgs, inStack,
    State.addr, List.append_eq, genLen, genE, genStp]
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

theorem gen_implies_post : ∀ s t, (keySearchContract abi stackUse).pre s →
    genContract.post s t → (keySearchContract abi stackUse).post s t := by
  sig_implies_post [keySearchContract, keySearchSig, abi, argRegs, reduceClassify, Loc.val,
    genContract, genPost, genResult, genRand, genE, genLen, genProgress, genStp, State.addr]

theorem gen_implies_pub (s t : State) (_hs : (keySearchContract abi stackUse).pre s)
    (_ht : (keySearchContract abi stackUse).pre t) (h : (keySearchContract abi stackUse).pub s t) :
    genContract.pub s t := by
  sig_pub [keySearchContract, keySearchSig, abi, argRegs, reduceClassify, Loc.val] at h
  obtain ⟨hsp, hleak, r0, r1, r2, r3, a0, a1, a2, a3⟩ := h
  have hl : (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt s.mem (BitVec.setWidth 64 (stackArg s 3)) 7)).length =
      (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt t.mem (BitVec.setWidth 64 (stackArg t 3)) 7)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range]
  obtain ⟨hab, htr⟩ := List.append_inj hleak (by simp only [List.length_append, hl, List.length_cons,
    List.length_nil])
  obtain ⟨hw, hc⟩ := List.append_inj hab hl
  simp only [List.cons.injEq, and_true] at hc
  refine ⟨hsp, r0, r1, r2, r3, fun j hj => ?_,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, hc.1, hc.2.1, hc.2.2, htr⟩
  match j, hj with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | _ + 4, h => omega

/-- Primes of 32 octets, an empty tape, disjoint buffers and the state's
words for the width. -/
private def genSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 288 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6005 then 0x80 else if a = 0x6008 then 0x20 else if a = 0x6009 then 0x04
    else if a = 0x600D then 0x40
    else if a = 0x4008 then 0x20 else if a = 0x4010 then 0x20 else if a = 0x4012 then 0x10 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x6000, 16⟩]
  wr := [⟨0x1000, 288⟩, ⟨0x2000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 56⟩]

theorem gen_implies : genContract.Implies (keySearchContract abi stackUse) where
  pre := gen_implies_pre
  post := gen_implies_post
  pub := gen_implies_pub
  sat := by
    refine ⟨genSat, ?_⟩
    sig_iff
    sig_reduce [keySearchContract, keySearchSig, abi, argRegs, reduceClassify, Loc.val, stackBelow,
      genContract, genPre, primeLenValid, State.addr]
    sig_and_intros
    all_goals first
      | exact Region.disjoint_of_sep (by decide +kernel)
      | decide +kernel

end VG.Proof.RsaKeyGen.Arm.Generate
