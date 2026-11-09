module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.Contract
public import VerifiedGarbage.Proof.Framework.Contract

-- separate module: its proofs build in parallel with those of `Correct` and `CT`, which `Verified` also imports

/-! # The controller's contract is its shared callable contract (AArch64) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG VG.AArch64 VG.Spec.RsaKeyGen

theorem gen_implies_pre (s : State) (h : (keySearchContract abi stackUse).pre s) : genContract.pre s := by
  sig_pre [keySearchContract, keySearchSig, abi, argRegs, stackBelow, genContract, genPre,
    inReads, inWrites, inKey, inUsed, inRand, inScr, inState, List.append_eq] at h
  sig_pre [keySearchContract, keySearchSig, abi, argRegs, stackBelow, genContract, genPre,
    inReads, inWrites, inKey, inUsed, inRand, inScr, inState, List.append_eq] at h
  sig_split h
  sig_reduce [keySearchContract, keySearchSig, abi, argRegs, stackBelow, genContract, genPre,
    inReads, inWrites, inKey, inUsed, inRand, inScr, inState, List.append_eq]
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
  sig_implies_post [keySearchContract, keySearchSig, abi, argRegs, genContract, genPost,
    genResult, genRand, genE, genLen, genProgress, List.append_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem gen_implies_pub (s t : State) (_hs : (keySearchContract abi stackUse).pre s)
    (_ht : (keySearchContract abi stackUse).pre t) (h : (keySearchContract abi stackUse).pub s t) :
    genContract.pub s t := by
  sig_pub [keySearchContract, keySearchSig, abi, argRegs, List.append_eq] at h
  obtain ⟨hsp, hleak, r0, r1, r2, r3, r4, r5, r6, r7⟩ := h
  have hl : (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt s.mem (s.gpr .x7) 7)).length =
      (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt t.mem (t.gpr .x7) 7)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range]
  obtain ⟨hab, htr⟩ := List.append_inj hleak (by simp only [List.length_append, hl, List.length_cons,
    List.length_nil])
  obtain ⟨hw, hc⟩ := List.append_inj hab hl
  simp only [List.cons.injEq, and_true] at hc
  exact ⟨hsp, r0, r1, r2, r3, r4, r5, r6, r7,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, hc.1, hc.2.1, hc.2.2, htr⟩

/-- Primes of 32 octets, an empty tape, disjoint buffers and the state's
words for the width. -/
private def genSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 288 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 0 | .x5 => 0x8000
    | .x6 => 1056 | .x7 => 0x4000 | _ => 0
  sp := 0x6000
  mem a := if a = 0x4008 then 0x20 else if a = 0x4010 then 0x20 else if a = 0x4012 then 0x10 else 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 288⟩, ⟨0x2000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 56⟩]

theorem gen_implies : genContract.Implies (keySearchContract abi stackUse) where
  pre := gen_implies_pre
  post := gen_implies_post
  pub := gen_implies_pub
  sat := by
    refine ⟨genSat, ?_⟩
    sig_iff
    sig_reduce [keySearchContract, keySearchSig, abi, argRegs, stackBelow, genContract,
      genPre, List.append_eq, primeLenValid]
    sig_and_intros
    all_goals first
      | exact Region.disjoint_of_sep (by decide +kernel)
      | decide +kernel

end VG.Proof.RsaKeyGen.AArch64.Generate
