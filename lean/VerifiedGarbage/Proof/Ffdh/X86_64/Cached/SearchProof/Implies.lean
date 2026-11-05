module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Contract
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.CachedSat
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.X86_64.Target

/-! # The key search's contract is its shared callable contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Spec.Ffdh

theorem stackArgs_nine (s : State) : List.map (stackArg s) (List.range 9) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5,
      stackArg s 6, stackArg s 7, stackArg s 8] := rfl

private theorem args_nowrap {s : State} (h : (s.gpr .rsp).toNat + 80 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 72 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.zero_add, Nat.mul_one]
  rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]
  simp only [BitVec.toNat_ofNat]
  omega

theorem key_implies_pre (s : State) (h : (cachedKeySearchContract abi 72).pre s) : keyContract.pre s := by
  sig_pre [cachedKeySearchContract, cachedKeySearchSig, keySearchSig, generationContextAt, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads, inContext, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_nine,
    List.append_eq] at h
  sig_pre [cachedKeySearchContract, cachedKeySearchSig, keySearchSig, generationContextAt, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads, inContext, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_nine,
    List.append_eq] at h
  sig_split h
  sig_reduce [cachedKeySearchContract, cachedKeySearchSig, keySearchSig, generationContextAt, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads, inContext, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_nine,
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

theorem key_implies_post : ∀ s t, (cachedKeySearchContract abi 72).pre s →
    keyContract.post s t → (cachedKeySearchContract abi 72).post s t := by
  sig_implies_post [cachedKeySearchContract, cachedKeySearchSig, keySearchSig, generationContextAt, abi, argRegs, keyContract, keyPost, keyResult,
    keyRand, keyA, keyDom, keyLen, keyRetries, stackArgs_nine, List.append_eq, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem key_implies_pub (s t : State) (_hs : (cachedKeySearchContract abi 72).pre s)
    (_ht : (cachedKeySearchContract abi 72).pre t) (h : (cachedKeySearchContract abi 72).pub s t) :
    keyContract.pub s t := by
  sig_pub [cachedKeySearchContract, cachedKeySearchSig, keySearchSig, generationContextAt, abi, argRegs, stackArgs_nine, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, rdi, rsi, rdx, rcx, r8, r9, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
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
  | 7, _ => exact a7
  | 8, _ => exact a8
  | _ + 9, h => omega

/-- A valid 64-octet domain (`CachedSat.domain`) and its context, an empty
tape, the controller's words and disjoint buffers. -/
private def keyBase (a : Addr) : Byte :=
  if a = 0x6008 then 0x80 else if a = 0x6010 then 0x40 else if a = 0x6019 then 0x70
  else if a = 0x6029 then 0x80 else if a = 0x6030 then 0x20 else if a = 0x6031 then 0x04
  else if a = 0x6039 then 0x40 else if a = 0x6042 then 0x10 else if a = 0x6048 then 0x13
  else if a = 0x6049 then 0x01 else if a = 0x4010 then 0x40 else CachedSat.domainMem a

private def keySat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x5000 | .r9 => 0x3000
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := CachedSat.withContext keyBase
  rd := [⟨0x3000, 128⟩, ⟨0x7000, 0⟩, ⟨0x100000, 2200⟩, ⟨0x6008, 72⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x5000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 128⟩]
  syms _ := 0

private theorem key_arg (i : Nat) (hi : i < 9) :
    stackArg keySat i = Mem.readW keyBase (0x6000 + BitVec.ofNat 64 (8 * (i + 1))) 64 := by
  unfold stackArg stackArgAddr
  refine CachedSat.readW_outside _ ?_
  have small : ∀ i < 9, (keySat.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))).toNat + 64 / 8 ≤ 0x100000 := by
    decide
  exact small i hi

private theorem a0 : stackArg keySat 0 = 128 := by rw [key_arg 0 (by decide)]; decide
private theorem a1 : stackArg keySat 1 = 64 := by rw [key_arg 1 (by decide)]; decide
private theorem a2 : stackArg keySat 2 = 0x7000 := by rw [key_arg 2 (by decide)]; decide
private theorem a3 : stackArg keySat 3 = 0 := by rw [key_arg 3 (by decide)]; decide
private theorem a4 : stackArg keySat 4 = 0x8000 := by rw [key_arg 4 (by decide)]; decide
private theorem a5 : stackArg keySat 5 = 1056 := by rw [key_arg 5 (by decide)]; decide
private theorem a6 : stackArg keySat 6 = 0x4000 := by rw [key_arg 6 (by decide)]; decide
private theorem a7 : stackArg keySat 7 = 0x100000 := by rw [key_arg 7 (by decide)]; decide
private theorem a8 : stackArg keySat 8 = 275 := by rw [key_arg 8 (by decide)]; decide

private theorem key_args : List.map (stackArg keySat) (List.range 9) =
    [128, 64, 0x7000, 0, 0x8000, 1056, 0x4000, 0x100000, 275] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append,
    a0, a1, a2, a3, a4, a5, a6, a7, a8]

private theorem key_domain : Spec.Rsa.bytesAt keySat.mem 0x3000 128 = CachedSat.domain := by
  rw [show keySat.mem = CachedSat.withContext keyBase from rfl, CachedSat.domain_unchanged]
  apply CachedSat.bytesAt_eq
  have : ∀ i < 128, keyBase (0x3000 + BitVec.ofNat 64 i) = CachedSat.domainMem (0x3000 + BitVec.ofNat 64 i) := by
    decide
  exact this

private theorem key_control (i : Nat) (hi : i < 3) : keySat.mem.readW (0x4000 + BitVec.ofNat 64 (8 * i)) 64 =
    Mem.readW keyBase (0x4000 + BitVec.ofNat 64 (8 * i)) 64 := by
  refine CachedSat.readW_outside _ ?_
  have small : ∀ i < 3, ((0x4000 : Addr) + BitVec.ofNat 64 (8 * i)).toNat + 64 / 8 ≤ 0x100000 := by decide
  exact small i hi

private theorem key_sat : ∃ s, (cachedKeySearchContract abi 72).pre s := by
  refine ⟨keySat, ?_⟩
  sig_pre [cachedKeySearchContract, cachedKeySearchSig, keySearchSig, pLenValid, domainLenValid,
    generationContextAt, abi, argRegs, key_args]
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8]
  repeat' apply And.intro
  all_goals first
    | rfl
    | decide
    | (apply Region.disjoint_of_sep; decide)
    | (change domainValid 64 (Spec.Rsa.bytesAt keySat.mem 0x3000 128) = true
       rw [key_domain]; exact CachedSat.domain_valid)
    | (change generationPrecompute 64 (Spec.Rsa.bytesAt keySat.mem 0x3000 128) =
          some (Spec.Rsa.wordsAt keySat.mem 0x100000 275)
       rw [key_domain]; exact (CachedSat.canonical keyBase).2)
    | (change (keySat.mem.readW 0x4000 64).toNat ≤ 128
       rw [show (0x4000 : Addr) = 0x4000 + BitVec.ofNat 64 (8 * 0) from rfl, key_control 0 (by decide)]; decide)
    | (change (keySat.mem.readW (0x4000 + 8) 64).toNat ≤ 128
       rw [show (0x4000 + 8 : Addr) = 0x4000 + BitVec.ofNat 64 (8 * 1) from rfl, key_control 1 (by decide)]; decide)
    | (change keySat.mem.readW (0x4000 + 16) 64 = BitVec.ofNat 64 64
       rw [show (0x4000 + 16 : Addr) = 0x4000 + BitVec.ofNat 64 (8 * 2) from rfl, key_control 2 (by decide)]; decide)

theorem key_implies : keyContract.Implies (cachedKeySearchContract abi 72) where
  pre := key_implies_pre
  post := key_implies_post
  pub := key_implies_pub
  sat := key_sat

end VG.Proof.Ffdh.X86_64.Cached.SearchProof
