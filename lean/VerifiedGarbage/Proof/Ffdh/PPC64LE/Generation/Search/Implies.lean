module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Contract
public import VerifiedGarbage.Spec.Ffdh.SievedContract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
meta import VerifiedGarbage.Proof.Framework.Contract

/-! # The parameter search's contract is its shared callable contract (PPC64LE)

Under `abi` for the state without the table (`search_implies_pre₀` and the
others, with `basePre` the precondition but the table's), then under
`abi.withConsts tables` (`pre_consts`, `post_consts`, `pub_consts`), whose
`ConstsOk` gives the table's region and entries.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Spec.Ffdh

/-- The table of trial division. -/
abbrev tables : List (String × List (BitVec 64)) := Impl.RsaKeyGen.TrialTable32.consts

/-- The buffers the controller only reads, but the table. -/
def inReads₀ (s : State) : List Region := [inRand s, inArgs s]

/-- The precondition without the table. -/
def basePre (s : State) : Prop :=
  s.sp.toNat + 32 + 8 * 10 ≤ 2 ^ 64 ∧ stackUse ≤ s.sp.toNat ∧
    s.rd = inReads₀ s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads₀ s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads₀ s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads₀ s, (below s.sp stackUse).Disjoint r) ∧
    512 ≤ genBits s ∧ genBits s ≤ 8192 ∧ genLen s = (genBits s + 7) / 8 ∧
    (genGen s = 2 ∨ genGen s = 5) ∧
    Spec.Rsa.scratchWords (genLen s) ≤ (stackArg s 0).toNat ∧
    genAttempts s ≤ parameterAttempts (genBits s) ∧
    s.mem.readW (stackArg s 1 + 8) 64 = BitVec.ofNat 64 (genLen s) ∧
    s.mem.readW (stackArg s 1 + 16) 64 = BitVec.ofNat 64 (parameterEntropy (genBits s)) ∧
    (s.gpr .r9).toNat ≤ parameterEntropy (genBits s)

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

private theorem args_nowrap {s : State} (h : s.sp.toNat + 32 + 8 * 10 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 16 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem search_implies_pre₀ (s : State) (h : (sievedParameterSearchContract abi stackUse).pre s) :
    basePre s := by
  sig_pre [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, basePre,
    inReads₀, inWrites, inOut, inUsed, inRand, inScr, inCtl, inArgs, stackArgs_two, List.append_eq] at h
  sig_pre [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, basePre,
    inReads₀, inWrites, inOut, inUsed, inRand, inScr, inCtl, inArgs, stackArgs_two, List.append_eq] at h
  sig_split h
  sig_reduce [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, basePre,
    inReads₀, inWrites, inOut, inUsed, inRand, inScr, inCtl, inArgs, stackArgs_two, List.append_eq]
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

theorem search_implies_post₀ : ∀ s t, True → searchPost s t → (sievedParameterSearchContract abi stackUse).post s t := by
  sig_implies_post [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, searchPost,
    searchResult, genRand, genLen, genBits, genGen, genAttempts, stackArgs_two, List.append_eq,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_implies_pub₀ (s t : State) (h : (sievedParameterSearchContract abi stackUse).pub s t) :
    s.sp = t.sp ∧ (genRand s).map (·.toNat) = (genRand t).map (·.toNat) ∧
    Spec.Rsa.wordsAt s.mem (stackArg s 1) 4 = Spec.Rsa.wordsAt t.mem (stackArg t 1) 4 ∧
    s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r5 = t.gpr .r5 ∧ s.gpr .r6 = t.gpr .r6 ∧
    (s.gpr .r7).setWidth 32 = (t.gpr .r7).setWidth 32 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9 ∧
    s.gpr .r10 = t.gpr .r10 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1 := by
  sig_pub [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackArgs_two, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, r3, r4, r5, r6, r7, r8, r9, r10, a0, a1⟩ := h
  have hl1 : (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)).length =
      (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt t.mem (t.gpr .r8) (t.gpr .r9).toNat)).length := by
    simp only [List.length_map, Spec.Rsa.bytesAt, List.length_range, r9]
  obtain ⟨hr, hw⟩ := List.append_inj hleak hl1
  exact ⟨hsp, hr, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, r3, r4, r5, r6, r7, r8, r9, r10,
    a0, a1⟩

private theorem tables_eq' :
    tables = [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)] := rfl

private theorem packed_length' : Impl.RsaKeyGen.TrialTable32.packed.length = 1024 :=
  Proof.RsaKeyGen.TrialTable32.packed_length

private theorem tab_mem : (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed) ∈ tables :=
  List.mem_singleton_self _

private theorem tab_regs (s : State) : constRegs tables s = [inTab s] := by
  rw [tables_eq', constRegs, Abi.constRegions_cons, Abi.constRegions_nil, packed_length']; rfl

/-- The precondition without the table, and what the table adds, are the
controller's. -/
theorem pre_of_base (s : State) (hb : basePre (stripConsts tables s)) (hc : ConstsOk tables stackUse s) :
    searchPre s := by
  obtain ⟨a1, a2, hrd, hwr, hnw, hpw, hwrd, hstk, b1, b2, l, g, sc, at', w8, w16, r9⟩ := hb
  have hrd' : (stripConsts tables s).rd = inReads₀ s := hrd
  have hwr' : s.wr = inWrites s := hwr
  have ht := hc.2.2.1 (inTab s) (by rw [tab_regs]; exact List.mem_singleton_self _)
  have hrd₂ : s.rd = inReads s := by
    rw [← List.take_append_drop (s.rd.length - tables.length) s.rd, hc.1, tab_regs]
    change (stripConsts tables s).rd ++ _ = _
    rw [hrd']; rfl
  have split : ∀ r ∈ inWrites s ++ inReads s, r ∈ inWrites s ++ inReads₀ s ∨ r = inTab s := by
    intro r hr
    simp only [inReads, inReads₀, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · exact .inl (.inr (.inr h))
    · exact .inr h
  refine ⟨a1, a2, hrd₂, hwr', fun r hr => ?_, hpw, fun w hw r hr => ?_, fun r hr => ?_, b1, b2, l, g, sc, at', w8,
    w16, r9, fun i hi => ?_⟩
  · rcases split r hr with h | rfl
    · exact hnw r h
    · exact ht.1
  · simp only [inReads, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hwrd w hw _ (List.mem_cons_self ..)
    · exact hwrd w hw _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact (ht.2.1 w (by rw [hwr']; exact hw)).symm
  · rcases split r hr with h | rfl
    · exact hstk r h
    · exact (ht.2.2 _ (by simp [abi, stackBelow, below])).symm
  · have e := hc.readW tab_mem (by rw [packed_length']; exact hi)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [packed_length']; exact hi), Option.getD_some,
      Proof.RsaKeyGen.TrialTable32.packed_entry hi] at e
    exact e

theorem search_implies_pre (s : State)
    (h : (sievedParameterSearchContract (abi.withConsts tables) stackUse).pre s) : searchContract.pre s := by
  unfold sievedParameterSearchContract at h
  rw [tables_eq'] at h
  obtain ⟨h₁, h₂⟩ := pre_consts.mp h
  exact pre_of_base s (search_implies_pre₀ _ h₁) h₂

theorem search_implies_post (s t : State) (_ : (sievedParameterSearchContract (abi.withConsts tables) stackUse).pre s)
    (h : searchContract.post s t) : (sievedParameterSearchContract (abi.withConsts tables) stackUse).post s t := by
  unfold sievedParameterSearchContract
  rw [tables_eq']
  exact post_consts.mpr (search_implies_post₀ s t trivial h)

theorem search_implies_pub (s t : State) (_ : (sievedParameterSearchContract (abi.withConsts tables) stackUse).pre s)
    (_ : (sievedParameterSearchContract (abi.withConsts tables) stackUse).pre t)
    (h : (sievedParameterSearchContract (abi.withConsts tables) stackUse).pub s t) : searchContract.pub s t := by
  unfold sievedParameterSearchContract at h
  rw [tables_eq'] at h
  obtain ⟨hp, hsy⟩ := pub_consts.mp h
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l, m, n⟩ := search_implies_pub₀ s t hp
  exact ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, hsy _ (List.mem_singleton_self _)⟩

/-! ## A state satisfying the precondition -/

/-- The words: `scratch_len` 1056 and the state at `0x4000`, at `0x6060`;
the state's words 0, 64 and the entropy cap of 512 bits. -/
def satSmall : Mem := fun a =>
  if a = 0x6060 then 0x20 else if a = 0x6061 then 0x04 else if a = 0x6069 then 0x40
  else if a = 0x4008 then 0x40 else if a = 0x4010 then 0x40 else if a = 0x4012 then 0x20 else 0

/-- The witness's memory: the small words, and the table at `0x20000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def satMem : Mem := fun a =>
  if (a - 0x1000).toNat < 0x10000 then satSmall a else constMem 0x20000 Impl.RsaKeyGen.TrialTable32.packed a

theorem satMem_held : ∀ i < Impl.RsaKeyGen.TrialTable32.packed.length,
    satMem.readW (0x20000 + BitVec.ofNat 64 (8 * i)) 64 = Impl.RsaKeyGen.TrialTable32.packed.getD i 0 := by
  intro i hi
  rw [← constMem_held _ _ (by rw [packed_length']; decide) i hi]
  refine Mem.readW_congr fun j hj => ?_
  have hn : ¬ (0x20000 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x1000 : Addr).toNat < 0x10000 := by
    rw [packed_length'] at hi
    simp only [Nat.reduceDiv] at hj
    have h1 : (0x20000 : Addr).toNat = 131072 := rfl
    have h2 : (0x1000 : Addr).toNat = 4096 := rfl
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h1, h2]
    omega
  unfold satMem
  simp only [hn, ↓reduceIte]

theorem satMem_small (a : Addr) (ha : (a - 0x1000).toNat + 8 ≤ 0x10000) :
    satMem.readW a 64 = satSmall.readW a 64 := by
  refine Mem.readW_congr fun j hj => ?_
  have hn : (a + BitVec.ofNat 64 j - 0x1000 : Addr).toNat < 0x10000 := by
    simp only [Nat.reduceDiv] at hj
    have h2 : (0x1000 : Addr).toNat = 4096 := rfl
    have := a.isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h2] at ha ⊢
    omega
  unfold satMem
  simp only [hn, ↓reduceIte]

/-- A 512-bit search with an empty tape, disjoint buffers, and the table. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 512 | .r7 => 2 | .r8 => 0x3000
    | .r10 => 0x8000 | _ => 0
  lr := 0
  sp := 0x6000
  mem := satMem
  rd := [⟨0x3000, 0⟩, ⟨0x6060, 16⟩, ⟨0x20000, 8192⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 128⟩]
  syms _ := 0x20000

theorem sat_arg (i : Nat) (hi : i < 2) :
    stackArg satState i = satSmall.readW (0x6000 + BitVec.ofNat 64 (32 + 8 * (8 + i))) 64 := by
  refine satMem_small _ ?_
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> decide

theorem sat_arg0 : stackArg satState 0 = 0x420 := (sat_arg 0 (by decide)).trans (by decide)
theorem sat_arg1 : stackArg satState 1 = 0x4000 := (sat_arg 1 (by decide)).trans (by decide)
theorem sat_w0 : satMem.readW 0x4000 64 = 0 := (satMem_small _ (by decide)).trans (by decide)
theorem sat_w8 : satMem.readW (0x4000 + 8) 64 = 64 := (satMem_small _ (by decide)).trans (by decide)
theorem sat_w16 : satMem.readW (0x4000 + 16) 64 = BitVec.ofNat 64 (parameterEntropy 512) :=
  (satMem_small _ (by decide)).trans (by decide)

theorem sat_base : (sievedParameterSearchContract abi stackUse).pre (stripConsts tables satState) := by
  have a0 : stackArg (stripConsts tables satState) 0 = 0x420 := sat_arg0
  have a1 : stackArg (stripConsts tables satState) 1 = 0x4000 := sat_arg1
  have w0 : (stripConsts tables satState).mem.readW 0x4000 64 = 0 := sat_w0
  have w8 : (stripConsts tables satState).mem.readW (0x4000 + 8) 64 = 64 := sat_w8
  have w16 : (stripConsts tables satState).mem.readW (0x4000 + 16) 64 = BitVec.ofNat 64 (parameterEntropy 512) :=
    sat_w16
  unfold sievedParameterSearchContract
  refine Sig.contract_pre_of_check (by decide +kernel) ?_
  sig_reduce [parameterSearchSig, abi, argRegs, stackArgs_two, List.append_eq, a0, a1, w0, w8, w16,
    parameterAttempts, parameterEntropy]
  sig_and_intros
  all_goals first
    | trivial
    | exact Region.disjoint_of_sep (by decide +kernel)
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
    · change r ∈ [⟨0x1000, 64⟩, ⟨0x2000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 128⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · change r ∈ stackBelow 0x6000 stackUse at hr
      simp only [stackBelow, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact Region.disjoint_of_sep (by decide)
  · rw [constRegs, Abi.constRegions_cons, Abi.constRegions_nil, hl]
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    decide

theorem sat : (sievedParameterSearchContract (abi.withConsts tables) stackUse).pre satState := by
  unfold sievedParameterSearchContract
  rw [tables_eq']
  have h₁ := sat_base
  have h₂ := sat_consts
  unfold sievedParameterSearchContract at h₁
  rw [tables_eq'] at h₁ h₂
  exact pre_consts.mpr ⟨h₁, h₂⟩

theorem search_implies : searchContract.Implies (sievedParameterSearchContract (abi.withConsts tables) stackUse) where
  pre := search_implies_pre
  post := search_implies_post
  pub := search_implies_pub
  sat := ⟨satState, sat⟩

end VG.Proof.Ffdh.PPC64LE.Generation
