module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Contract
public import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
meta import VerifiedGarbage.Proof.Framework.Contract

-- separate module: its proofs build in parallel with those of `Correct` and `CT`, which `Verified` also imports

/-! # The search's contract is its shared callable contract (RISCV64)

Under `abi` for the state without the table (`search_implies_pre₀` and the
others), then under `abi.withConsts tables` (`pre_consts`, `post_consts`,
`pub_consts`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Search

open VG VG.RISCV64 VG.Spec.RsaKeyGen

theorem stackArgs_four (s : State) : List.map (stackArg s) (List.range 4) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

private theorem args_nowrap {s : State} (h : s.sp.toNat + 32 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 32 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  exact h

theorem search_implies_pre₀ (s : State) (h : (primeSearchContract abi stackUse).pre s) : basePre s := by
  sig_pre [primeSearchContract, primeSearchSig, abi, argRegs, stackBelow, basePre,
    inReads, inWrites, inOut, inUsed, inE, inP, inRand, inScr, inState, inArgs, stackArgs_four,
    List.append_eq] at h
  sig_pre [primeSearchContract, primeSearchSig, abi, argRegs, stackBelow, basePre,
    inReads, inWrites, inOut, inUsed, inE, inP, inRand, inScr, inState, inArgs, stackArgs_four,
    List.append_eq] at h
  sig_split h
  sig_reduce [primeSearchContract, primeSearchSig, abi, argRegs, stackBelow, basePre,
    inReads, inWrites, inOut, inUsed, inE, inP, inRand, inScr, inState, inArgs, stackArgs_four,
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

theorem search_implies_post₀ : ∀ s t, True → searchPost s t → (primeSearchContract abi stackUse).post s t := by
  sig_implies_post [primeSearchContract, primeSearchSig, abi, argRegs, searchPost,
    searchResult, searchRand, searchE, searchP, searchLen, searchRemaining, stackArgs_four,
    List.append_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_implies_pub₀ (s t : State) (h : (primeSearchContract abi stackUse).pub s t) :
    s.sp = t.sp ∧
    s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1 ∧ s.gpr .a2 = t.gpr .a2 ∧ s.gpr .a3 = t.gpr .a3 ∧
    s.gpr .a4 = t.gpr .a4 ∧ s.gpr .a5 = t.gpr .a5 ∧ s.gpr .a6 = t.gpr .a6 ∧ s.gpr .a7 = t.gpr .a7 ∧
    (∀ j < 4, stackArg s j = stackArg t j) ∧
    searchE s = searchE t ∧ Spec.Rsa.wordsAt s.mem (stackArg s 3) 4 = Spec.Rsa.wordsAt t.mem (stackArg t 3) 4 ∧
    (searchResult s).status = (searchResult t).status ∧ (searchResult s).used = (searchResult t).used ∧
    (requested (searchLen s) (searchResult s)) = (requested (searchLen t) (searchResult t)) ∧
    (searchResult s).trace = (searchResult t).trace := by
  sig_pub [primeSearchContract, primeSearchSig, abi, argRegs, stackArgs_four, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, r3, r4, r5, r6, r7, r8, r9, r10, a0, a1, a2, a3⟩ := h
  have hl1 : (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)).length =
      (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt t.mem (t.gpr .a3) (t.gpr .a4).toNat)).length := by
    simp only [List.length_map, Spec.Rsa.bytesAt, List.length_range, r7]
  have hl2 : (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt s.mem (stackArg s 3) 4)).length =
      (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt t.mem (stackArg t 3) 4)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range]
  obtain ⟨habc, htr⟩ := List.append_inj hleak (by simp only [List.length_append, hl1, hl2, List.length_cons,
    List.length_nil])
  obtain ⟨hab, hc⟩ := List.append_inj habc (by simp only [List.length_append, hl1, hl2])
  obtain ⟨he, hw⟩ := List.append_inj hab hl1
  simp only [List.cons.injEq, and_true] at hc
  refine ⟨hsp, r3, r4, r5, r6, r7, r8, r9, r10, fun j hj => ?_,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, hc.1, hc.2.1,
    (by rw [show searchLen s = searchLen t from congrArg BitVec.toNat r4]
        exact Entropy.requested_congr hc.1 hc.2.2), htr⟩
  match j, hj with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | _ + 4, h => omega

private theorem tables_eq' :
    tables = [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)] := rfl

theorem search_implies_pre (s : State)
    (h : (primeSearchContract (abi.withConsts tables) stackUse).pre s) : searchContract.pre s := by
  unfold primeSearchContract at h
  rw [tables_eq'] at h
  obtain ⟨h₁, h₂⟩ := pre_consts.mp h
  exact ⟨search_implies_pre₀ _ h₁, h₂⟩

theorem search_implies_post (s t : State) (_ : (primeSearchContract (abi.withConsts tables) stackUse).pre s)
    (h : searchContract.post s t) : (primeSearchContract (abi.withConsts tables) stackUse).post s t := by
  unfold primeSearchContract
  rw [tables_eq']
  exact post_consts.mpr (search_implies_post₀ s t trivial h)

theorem search_implies_pub (s t : State) (_ : (primeSearchContract (abi.withConsts tables) stackUse).pre s)
    (_ : (primeSearchContract (abi.withConsts tables) stackUse).pre t)
    (h : (primeSearchContract (abi.withConsts tables) stackUse).pub s t) : searchContract.pub s t := by
  unfold primeSearchContract at h
  rw [tables_eq'] at h
  obtain ⟨hp, hsy⟩ := pub_consts.mp h
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o, q, r⟩ := search_implies_pub₀ s t hp
  exact ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o, q, r, hsy _ (List.mem_singleton_self _)⟩

/-! ## A state satisfying the precondition -/

private theorem packed_length' : Impl.RsaKeyGen.TrialTable32.packed.length = 1024 :=
  Proof.RsaKeyGen.TrialTable32.packed_length

/-- The stack arguments and the state's words: `rand_len` 0, `scratch` at
`0x10000`, `scratch_len` 544 and the state at `0x4000`, at `0x8000`; the
state's words 0, 32 and `32769 · 32`. -/
def satSmall : Mem := fun a =>
  if a = 0x800A then 1 else if a = 0x8010 then 0x20 else if a = 0x8011 then 2
  else if a = 0x8019 then 0x40 else if a = 0x4008 then 0x20 else if a = 0x4010 then 0x20
  else if a = 0x4012 then 0x10 else 0

/-- The witness's memory: the small words, and the table at `0x20000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def satMem : Mem := fun a =>
  if (a - 0x4000).toNat < 0x4020 then satSmall a else constMem 0x20000 Impl.RsaKeyGen.TrialTable32.packed a

theorem satMem_held : ∀ i < Impl.RsaKeyGen.TrialTable32.packed.length,
    satMem.readW (0x20000 + BitVec.ofNat 64 (8 * i)) 64 = Impl.RsaKeyGen.TrialTable32.packed.getD i 0 := by
  intro i hi
  rw [← constMem_held _ _ (by rw [packed_length']; decide) i hi]
  refine Mem.readW_congr fun j hj => ?_
  have hn : ¬ (0x20000 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x4000 : Addr).toNat < 0x4020 := by
    rw [packed_length'] at hi
    simp only [Nat.reduceDiv] at hj
    have h1 : (0x20000 : Addr).toNat = 131072 := rfl
    have h2 : (0x4000 : Addr).toNat = 16384 := rfl
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h1, h2]
    omega
  unfold satMem
  simp only [hn, ↓reduceIte]

theorem satMem_small (a : Addr) (ha : (a - 0x4000).toNat + 8 ≤ 0x4020) :
    satMem.readW a 64 = satSmall.readW a 64 := by
  refine Mem.readW_congr fun j hj => ?_
  have hn : (a + BitVec.ofNat 64 j - 0x4000 : Addr).toNat < 0x4020 := by
    simp only [Nat.reduceDiv] at hj
    have h2 : (0x4000 : Addr).toNat = 16384 := rfl
    have := a.isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h2] at ha ⊢
    omega
  unfold satMem
  simp only [hn, ↓reduceIte]

/-- A 32-byte prime, `e = 0` of one octet, no other prime, an empty tape,
disjoint buffers, the state's words for the width, and the table. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 32 | .a2 => 0x2000 | .a3 => 0x3000 | .a4 => 1 | .a5 => 0x5000
    | .a7 => 0x7000 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := [⟨0x3000, 1⟩, ⟨0x5000, 0⟩, ⟨0x7000, 0⟩, ⟨0x8000, 32⟩, ⟨0x20000, 8192⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 8⟩, ⟨0x10000, 544 * 8⟩, ⟨0x4000, 32⟩]
  syms _ := 0x20000

theorem sat_arg (i : Nat) (hi : i < 4) :
    stackArg satState i = satSmall.readW (0x8000 + BitVec.ofNat 64 (8 * i)) 64 := by
  refine satMem_small _ ?_
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> decide

theorem sat_arg0 : stackArg satState 0 = 0 := (sat_arg 0 (by decide)).trans (by decide)
theorem sat_arg1 : stackArg satState 1 = 0x10000 := (sat_arg 1 (by decide)).trans (by decide)
theorem sat_arg2 : stackArg satState 2 = 544 := (sat_arg 2 (by decide)).trans (by decide)
theorem sat_arg3 : stackArg satState 3 = 0x4000 := (sat_arg 3 (by decide)).trans (by decide)
theorem sat_w0 : satMem.readW 0x4000 64 = 0 := (satMem_small _ (by decide)).trans (by decide)
theorem sat_w8 : satMem.readW (0x4000 + 8) 64 = 32 := (satMem_small _ (by decide)).trans (by decide)
theorem sat_w16 : satMem.readW (0x4000 + 16) 64 = BitVec.ofNat 64 (primeEntropy 32) :=
  (satMem_small _ (by decide)).trans (by decide)

theorem sat_base : (primeSearchContract abi stackUse).pre (stripConsts tables satState) := by
  have a0 : stackArg (stripConsts tables satState) 0 = 0 := sat_arg0
  have a1 : stackArg (stripConsts tables satState) 1 = 0x10000 := sat_arg1
  have a2 : stackArg (stripConsts tables satState) 2 = 544 := sat_arg2
  have a3 : stackArg (stripConsts tables satState) 3 = 0x4000 := sat_arg3
  have w0 : (stripConsts tables satState).mem.readW 0x4000 64 = 0 := sat_w0
  have w8 : (stripConsts tables satState).mem.readW (0x4000 + 8) 64 = 32 := sat_w8
  have w16 : (stripConsts tables satState).mem.readW (0x4000 + 16) 64 = BitVec.ofNat 64 (primeEntropy 32) :=
    sat_w16
  unfold primeSearchContract
  refine Sig.contract_pre_of_check (by decide +kernel) ?_
  sig_reduce [primeSearchSig, abi, argRegs, stackArgs_four, List.append_eq, a0, a1, a2, a3, w0, w8, w16]
  sig_and_intros
  all_goals first
    | trivial
    | decide +kernel

theorem sat_consts : ConstsOk tables stackUse satState := by
  have hl := packed_length'
  have held := satMem_held
  rw [tables_eq']
  generalize Impl.RsaKeyGen.TrialTable32.packed = W at hl held ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [constRegs, Abi.constRegions_cons, Abi.constRegions_nil, hl]; rfl
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact held
  · rw [constRegs, Abi.constRegions_cons, Abi.constRegions_nil, hl]
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    refine ⟨by decide, fun r hr => ?_, fun r hr => ?_⟩
    · change r ∈ [⟨0x1000, 32⟩, ⟨0x2000, 8⟩, ⟨0x10000, 544 * 8⟩, ⟨0x4000, 32⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · change r ∈ stackBelow 0x8000 stackUse at hr
      simp only [stackBelow, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact Region.disjoint_of_sep (by decide)
  · rw [constRegs, Abi.constRegions_cons, Abi.constRegions_nil, hl]
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    decide

theorem sat : (primeSearchContract (abi.withConsts tables) stackUse).pre satState := by
  unfold primeSearchContract
  rw [tables_eq']
  have h₁ := sat_base
  have h₂ := sat_consts
  unfold primeSearchContract at h₁
  rw [tables_eq'] at h₁ h₂
  exact pre_consts.mpr ⟨h₁, h₂⟩

theorem search_implies : searchContract.Implies (primeSearchContract (abi.withConsts tables) stackUse) where
  pre := search_implies_pre
  post := search_implies_post
  pub := search_implies_pub
  sat := ⟨satState, sat⟩

end VG.Proof.RsaKeyGen.RISCV64.Search
