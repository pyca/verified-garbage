module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.SearchProof.Data
public import VerifiedGarbage.Impl.Ffdh.RISCV64.CachedSearch
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Ffdh.RISCV64.Cached
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.AttemptCorrect
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.AttemptCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Ffdh.CachedSat
import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.SearchProof.Correct
import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.SearchProof.CT

/-! # The verified cached key search (RISC-V)

`keyContract` states the shared contract on the registers and the stack
(`key_implies`); with correctness (`key_correct`) and constant time
(`key_constantTime`), the cached key search is verified for any attempt that
uses no stack of its own (`key_verified_of`), and for
`vg_ffdh_generate_key_cached` (`cachedAttempt`, `search_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached.SearchProof

open VG VG.RISCV64 VG.Spec.Ffdh

theorem stackArgs_seven (s : State) : List.map (stackArg s) (List.range 7) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6] := rfl

private theorem args_nowrap {s : State} (h : s.sp.toNat + 56 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 56 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  exact h

theorem key_implies_pre (s : State) (h : (cachedKeySearchContract RISCV64.abi stackUse).pre s) : keyContract.pre s := by
  sig_pre [cachedKeySearchContract, cachedKeySearchSig, keySearchSig, Spec.Ffdh.generationContextAt, RISCV64.abi, argRegs, stackBelow, keyContract, keyPre,
    inReads, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inContext, inArgs, stackArgs_seven,
    List.append_eq] at h
  sig_pre [cachedKeySearchContract, cachedKeySearchSig, keySearchSig, Spec.Ffdh.generationContextAt, RISCV64.abi, argRegs, stackBelow, keyContract, keyPre,
    inReads, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inContext, inArgs, stackArgs_seven,
    List.append_eq] at h
  sig_split h
  sig_reduce [cachedKeySearchContract, cachedKeySearchSig, keySearchSig, Spec.Ffdh.generationContextAt, RISCV64.abi, argRegs, stackBelow, keyContract, keyPre,
    inReads, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inContext, inArgs, stackArgs_seven,
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

theorem key_implies_post : ∀ s t, (cachedKeySearchContract RISCV64.abi stackUse).pre s →
    keyContract.post s t → (cachedKeySearchContract RISCV64.abi stackUse).post s t := by
  sig_implies_post [cachedKeySearchContract, cachedKeySearchSig, keySearchSig, Spec.Ffdh.generationContextAt, RISCV64.abi, argRegs, keyContract, keyPost, keyResult,
    keyRand, keyA, keyDom, keyLen, keyRetries, stackArgs_seven, List.append_eq, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem key_implies_pub (s t : State) (_hs : (cachedKeySearchContract RISCV64.abi stackUse).pre s)
    (_ht : (cachedKeySearchContract RISCV64.abi stackUse).pre t) (h : (cachedKeySearchContract RISCV64.abi stackUse).pub s t) :
    keyContract.pub s t := by
  sig_pub [cachedKeySearchContract, cachedKeySearchSig, keySearchSig, Spec.Ffdh.generationContextAt, RISCV64.abi, argRegs, stackArgs_seven, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6⟩ := h
  have hl1 : (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)).length =
      (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt t.mem (t.gpr .a5) (t.gpr .a6).toNat)).length := by
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
  | 5, _ => exact a5
  | 6, _ => exact a6
  | _ + 7, h => omega

/-- The stack's bytes: `rand` `0x7000`, `rand_len` 0, `scratch` `0x8000`,
`scratch_len` 1056, `state` `0x4000`, `ctx` `0x100000` and `ctx_len` 275, at
`0x6000`; the state's width 64; the domain of `CachedSat` at `0x3000`. -/
private def keyBase (a : Addr) : Byte :=
  if a = 0x6001 then 0x70 else if a = 0x6011 then 0x80 else if a = 0x6018 then 0x20
  else if a = 0x6019 then 0x04 else if a = 0x6021 then 0x40 else if a = 0x602a then 0x10
  else if a = 0x6030 then 0x13 else if a = 0x6031 then 0x01 else if a = 0x4010 then 0x40
  else CachedSat.domainMem a

/-- A state meeting the contract, with an empty tape and the domain's
context at `0x100000`. -/
private def keySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x5000 | .a5 => 0x3000
    | .a6 => 128 | .a7 => 64 | _ => 0
  sp := 0x6000
  mem := CachedSat.withContext keyBase
  rd := [⟨0x3000, 128⟩, ⟨0x7000, 0⟩, ⟨0x100000, 2200⟩, ⟨0x6000, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x5000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 128⟩]

private theorem key_arg (i : Nat) (hi : i < 7) :
    stackArg keySat i = Mem.readW keyBase (0x6000 + BitVec.ofNat 64 (8 * i)) 64 := by
  unfold stackArg stackArgAddr
  rw [show keySat.sp = 0x6000 from rfl]
  refine CachedSat.readW_outside _ ?_
  have small : ∀ i < 7, ((0x6000 : BitVec 64) + BitVec.ofNat 64 (8 * i)).toNat + 64 / 8 ≤ 0x100000 := by
    decide
  exact small i hi

private theorem a0 : stackArg keySat 0 = 0x7000 := by rw [key_arg 0 (by decide)]; decide
private theorem a1 : stackArg keySat 1 = 0 := by rw [key_arg 1 (by decide)]; decide
private theorem a2 : stackArg keySat 2 = 0x8000 := by rw [key_arg 2 (by decide)]; decide
private theorem a3 : stackArg keySat 3 = 1056 := by rw [key_arg 3 (by decide)]; decide
private theorem a4 : stackArg keySat 4 = 0x4000 := by rw [key_arg 4 (by decide)]; decide
private theorem a5 : stackArg keySat 5 = 0x100000 := by rw [key_arg 5 (by decide)]; decide
private theorem a6 : stackArg keySat 6 = 275 := by rw [key_arg 6 (by decide)]; decide

private theorem key_control (i : Nat) (hi : i < 3) : keySat.mem.readW (0x4000 + BitVec.ofNat 64 (8 * i)) 64 =
    Mem.readW keyBase (0x4000 + BitVec.ofNat 64 (8 * i)) 64 := by
  refine CachedSat.readW_outside _ ?_
  have small : ∀ i < 3, ((0x4000 : Addr) + BitVec.ofNat 64 (8 * i)).toNat + 64 / 8 ≤ 0x100000 := by decide
  exact small i hi

private theorem key_domain : Spec.Rsa.bytesAt keySat.mem 0x3000 128 = CachedSat.domain := by
  rw [show keySat.mem = CachedSat.withContext keyBase from rfl, CachedSat.domain_unchanged]
  apply CachedSat.bytesAt_eq
  have : ∀ i < 128, keyBase (0x3000 + BitVec.ofNat 64 i) = CachedSat.domainMem (0x3000 + BitVec.ofNat 64 i) := by
    decide
  exact this

theorem key_sat : ∃ s, (cachedKeySearchContract RISCV64.abi stackUse).pre s := by
  refine ⟨keySat, ?_⟩
  sig_pre [cachedKeySearchContract, cachedKeySearchSig, keySearchSig, pLenValid, domainLenValid,
    Spec.Ffdh.generationContextAt, RISCV64.abi, argRegs, stackArgs_seven]
  simp only [a0, a1, a2, a3, a4, a5, a6]
  repeat' apply And.intro
  all_goals first
    | rfl
    | decide
    | (apply Region.disjoint_of_sep; decide)
    | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt keySat.mem 0x3000 128) = true
       rw [key_domain]; exact CachedSat.domain_valid)
    | (change Spec.Ffdh.generationPrecompute 64 (Spec.Rsa.bytesAt keySat.mem 0x3000 128) =
          some (Spec.Rsa.wordsAt keySat.mem 0x100000 275)
       rw [key_domain]; exact (CachedSat.canonical keyBase).2)
    | (change (keySat.mem.readW 0x4000 64).toNat ≤ 128
       rw [show (0x4000 : Addr) = 0x4000 + BitVec.ofNat 64 (8 * 0) from rfl, key_control 0 (by decide)]; decide)
    | (change (keySat.mem.readW (0x4000 + 8) 64).toNat ≤ 128
       rw [show (0x4000 + 8 : Addr) = 0x4000 + BitVec.ofNat 64 (8 * 1) from rfl, key_control 1 (by decide)]
       decide)
    | (change keySat.mem.readW (0x4000 + 16) 64 = BitVec.ofNat 64 64
       rw [show (0x4000 + 16 : Addr) = 0x4000 + BitVec.ofNat 64 (8 * 2) from rfl, key_control 2 (by decide)]
       decide)

theorem key_implies : keyContract.Implies (cachedKeySearchContract RISCV64.abi stackUse) where
  pre := key_implies_pre
  post := key_implies_post
  pub := key_implies_pub
  sat := key_sat

theorem key_verified_of (a : Attempt) :
    Verified RISCV64.target (Impl.Ffdh.RISCV64.Cached.Search.code a.call)
      (cachedKeySearchContract RISCV64.abi stackUse) :=
  Verified.of_correct (key_correct a) (key_constantTime a) key_implies

/-- `vg_ffdh_generate_key_cached`, which has no frames. -/
def cachedAttempt : Attempt where
  name := Spec.Ffdh.cachedGenerateKeyApi.name
  code := Impl.Ffdh.RISCV64.Cached.Generate.code
  stack := by decide
  correct := Cached.cg_correct
  ct := Cached.cg_ct

/-- The cached key search calling it. -/
abbrev keyCode : Prog isa := Impl.Ffdh.RISCV64.Cached.Search.code cachedAttempt.call

theorem search_verified :
    Verified RISCV64.target keyCode (cachedKeySearchContract RISCV64.abi stackUse) :=
  key_verified_of cachedAttempt

end VG.Proof.Ffdh.RISCV64.Cached.SearchProof
