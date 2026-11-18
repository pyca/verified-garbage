module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Backend
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.ParameterCandidate
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Contract
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.CTCode
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Main
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Trial.Loop
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Trial.Loop
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Main
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.TestsFn
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.TestsFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Tests
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Tests
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Mr
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Mr
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.DrawFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCallCT
import VerifiedGarbage.Proof.Framework.RelCTChain
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.DrawFn
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCallCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.RelCTChain
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Contract
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Base
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.GeFlag
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Contract
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Base
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.GeFlag
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Ffdh.Contract
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Ffdh.PPC64LE.Generation.Search.Implies`, which only this module used -/

section

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
  omega_using [h]

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
    omega_using [hi, hj]
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
    omega_using [hj, ha]
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
  have : i = 0 ∨ i = 1 := by omega_using [hi]
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

end

end

/-! ### `Ffdh.PPC64LE.ParameterCandidate.CT`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Correct`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Entry`, which this module and modules that import it used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: the entry

`entryA_ok`: `scratch_len` from the stack, the save area's address in
`r11`, the link register saved.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.MillerRabin.PPC64LE.Search (rw_off rw_self)
open VG.Impl.MillerRabin.PPC64LE.Search (sth ldh hWsLen hUsed hRand hRandLen)

theorem entryA_ok {s : State} {B : Addr} {n : Nat} (h10 : s.gpr .r10 = B) (hn : stackArg s 0 = BitVec.ofNat 64 n)
    (hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) (hn160 : 160 ≤ 8 * n)
    (hsv : InRegions s.wr (off B (8 * n - 160 + 144)) 8) :
    WP isa (.block [.addSp .r11 96, .load .d .r12 .r11 0, .lsl .r11 .r12 3, .add .r11 .r10 .r11,
      .subi .r11 .r11 saveBytes, .mflr .r0, .store .d .r0 .r11 144]) s fun t =>
      (t.gpr .r11 = off B (8 * n - 160) ∧ t.gpr .r12 = BitVec.ofNat 64 n ∧
        t.mem = s.mem.writeW (off B (8 * n - 160 + 144)) s.lr) ∧ Keep [.r0, .r11, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [stackArgAddr, stackArg, Nat.reduceMul, Nat.reduceAdd] at hargs hn
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  have e1 : B + BitVec.ofNat 64 (8 * n) - BitVec.ofNat 64 160 = off B (8 * n - 160) :=
    VG.Offset.add_ofNat_sub B hn160
  prun [ea, hargs, hn, h10, Pub.ofNat_shl3, saveBytes, e1, exec_mflr, off_add, hsv]

/-- The first `k` registers saved, from the state `s₀` after `entryA`. -/
structure SV (B : Addr) (n : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  out : Outside B (8 * n - 160) 160 s₀.mem s.mem
  saved : ∀ i < k, word s.mem B (8 * n - 160 + 8 * i) = s₀.gpr (Impl.Ffdh.PPC64LE.ParameterCandidate.saved i)
  lrW : word s.mem B (8 * n - 160 + 144) = word s₀.mem B (8 * n - 160 + 144)

theorem save_step {B : Addr} {n : Nat} {s₀ : State} (h11 : s₀.gpr .r11 = off B (8 * n - 160))
    (hn160 : 160 ≤ 8 * n) (hn : 8 * n ≤ 2 ^ 64)
    (hin : ∀ i < 18, InRegions s₀.wr (off B (8 * n - 160 + 8 * i)) 8) {k : Nat} (hk : k < 18) {s : State}
    (h : SV B n s₀ k s) : WP isa (.block [.store .d (Impl.Ffdh.PPC64LE.ParameterCandidate.saved k) .r11 (8 * k)]) s (SV B n s₀ (k + 1)) := by
  have hw : s.gpr .r11 = off B (8 * n - 160) := by rw [h.gpr, h11]
  have hout : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [h.wr, hw, off_add]; exact hin k hk
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show Reg.r11 ≠ .r0 by decide) (show 8 * k < 2 ^ 15 ∧ (8 * k) % 4 = 0 by omega_using [hk]) hout,
    Option.some.injEq, exists_eq_left', hw, off_add]
  have hW := writeW_outside s.mem B (d := 8 * n - 160 + 8 * k) (s.gpr (Impl.Ffdh.PPC64LE.ParameterCandidate.saved k)) (by omega_using [hn, hk])
  refine ⟨h.gpr, h.rd, h.wr, h.sp, h.lr, h.out.trans (hW.mono (by omega_using []) (by omega_using [hk])), fun i hi => ?_, ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · simp only [word, off]
      rw [rw_off _ _ _ (by omega_using [hi]) (by omega_using [hn, hk]) (by omega_arith)]
      exact h.saved i hi
    · simp only [word, off]; rw [rw_self, h.gpr]
  · simp only [word, off] at h ⊢
    rw [rw_off _ _ _ (by omega_using [hk]) (by omega_using [hn, hk]) (by omega_using [hn])]
    exact h.lrW

theorem map_flatMap {α β : Type} (g : α → β) (l : List α) : l.map g = l.flatMap fun i => [g i] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem saves_ok {B : Addr} {n : Nat} {s₀ : State} (h11 : s₀.gpr .r11 = off B (8 * n - 160))
    (hn160 : 160 ≤ 8 * n) (hn : 8 * n ≤ 2 ^ 64)
    (hin : ∀ i < 18, InRegions s₀.wr (off B (8 * n - 160 + 8 * i)) 8) :
    WP isa (.block ((List.range 18).map fun i => .store .d (Impl.Ffdh.PPC64LE.ParameterCandidate.saved i) .r11 (8 * i))) s₀ (SV B n s₀ 18) := by
  rw [map_flatMap]
  exact wp_range_flatMap (M := isa) (SV B n s₀) (fun k s hk h => save_step h11 hn160 hn hin hk h) 18
    (Nat.le_refl _) s₀ ⟨rfl, rfl, rfl, rfl, rfl, Outside.refl _ _ _ _, fun _ h => absurd h (by omega_using []), rfl⟩

/-- The header's stores. -/
def hdrW (m : Mem) (B : Addr) (r12 r3 r4 r5 r6 r7 r8 r9 : BitVec 64) : Mem :=
  ((((((((m.writeW (B + BitVec.ofNat 64 0) r12).writeW (B + BitVec.ofNat 64 16) r3).writeW
    (B + BitVec.ofNat 64 24) r4).writeW (B + BitVec.ofNat 64 152) r4).writeW (B + BitVec.ofNat 64 32) r5).writeW
    (B + BitVec.ofNat 64 40) r6).writeW (B + BitVec.ofNat 64 128) r7).writeW (B + BitVec.ofNat 64 136) r8).writeW
    (B + BitVec.ofNat 64 144) r9

theorem header_ok {s : State} {B : Addr} (h10 : s.gpr .r10 = B)
    (hst : ∀ d, d + 8 ≤ 256 → InRegions s.wr (B + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.addi .r31 .r10 0, sth .r12 hWsLen, sth .r3 hOut, sth .r4 hLen, sth .r4 hUsed, sth .r5 hUsedP,
      sth .r6 hBits, .lsr .w .r7 .r7 0, sth .r7 hGen, sth .r8 hRand, sth .r9 hRandLen]) s fun t =>
      (t.gpr .r31 = B ∧ t.gpr .r7 = ((s.gpr .r7).setWidth 32).setWidth 64 ∧
        t.mem = hdrW s.mem B (s.gpr .r12) (s.gpr .r3) (s.gpr .r4) (s.gpr .r5) (s.gpr .r6)
          (((s.gpr .r7).setWidth 32).setWidth 64) (s.gpr .r8) (s.gpr .r9)) ∧ Keep [.r7, .r31] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [sth, hWsLen, hOut, hLen, hUsed, hUsedP, hBits, hGen, hRand,
    hRandLen]
  prun [h10, hst 0 (by decide), hst 16 (by decide), hst 24 (by decide), hst 152 (by decide),
    hst 32 (by decide), hst 40 (by decide), hst 128 (by decide), hst 136 (by decide), hst 144 (by decide),
    BitVec.ushiftRight_zero]
  exact ⟨BitVec.add_zero B, rfl⟩

theorem hdrW_words (m : Mem) (B : Addr) (r12 r3 r4 r5 r6 r7 r8 r9 : BitVec 64) :
    let h := hdrW m B r12 r3 r4 r5 r6 r7 r8 r9
    word h B 0 = r12 ∧ word h B 16 = r3 ∧ word h B 24 = r4 ∧ word h B 152 = r4 ∧ word h B 32 = r5 ∧
      word h B 40 = r6 ∧ word h B 128 = r7 ∧ word h B 136 = r8 ∧ word h B 144 = r9 := by
  simp (disch := decide) only [hdrW, word, off, rw_off, rw_self, and_self]

theorem hdrW_frm (m : Mem) (B : Addr) (r12 r3 r4 r5 r6 r7 r8 r9 : BitVec 64) :
    Frm B [(0, 256)] m (hdrW m B r12 r3 r4 r5 r6 r7 r8 r9) := by
  unfold hdrW
  iterate 9 (refine VG.Proof.MillerRabin.PPC64LE.Search.frm_writeW ?_ _ ⟨(0, 256), List.mem_singleton_self _, by decide, by decide⟩ (by decide))
  exact Frm.refl _ _ _

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Front`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.ParameterCandidate.ZeroOut`, which only this module used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: `out` zeroed

`zeroOut_ok`: `out`'s `k` bytes := 0, nothing else in memory changed.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE

theorem zeroOut_ok {s : State} {B O : Addr} {Z k : Nat} (hs : Scr s B Z) (ho : Scr s O k)
    (h31 : s.gpr .r31 = B)
    (hO : s.mem.readW (B + BitVec.ofNat 64 16) 64 = O) (hL : s.mem.readW (B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hk' : k < 2 ^ 63) (hZ : 32 ≤ Z) :
    WP isa zeroOut s fun t =>
      ((∀ i < k, t.mem (off O i) = 0) ∧ Outside O 0 k s.mem t.mem) ∧ Keep [.r0, .r4, .r5] s t := by
  have hno := ho.nowrap
  unfold zeroOut
  refine WP.seq ?_
  refine WP.mono (WP.keep [.r0, .r4, .r5] (Q := fun s₂ => s₂.gpr .r4 = O ∧ s₂.gpr .r5 = BitVec.ofNat 64 k ∧
    s₂.gpr .r0 = BitVec.ofNat 64 0 ∧ s₂.mem = s.mem)
    (by simp only [Impl.MillerRabin.PPC64LE.Search.ldh, hOut, hLen]
        prun [h31, hO, hL, hs.ld (d := 16) (n := 8) (by omega_arith), hs.ld (d := 24) (n := 8) (by omega_arith)])
    (by decide)) fun s₂ ⟨⟨b4, b5, b0, m2⟩, k2⟩ => ?_
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .r4 = off O j ∧ t.gpr .r0 = BitVec.ofNat 64 0 ∧ Outside O 0 j s.mem t.mem ∧
      (∀ i < j, t.mem (off O i) = 0) ∧ Keep [.r0, .r4, .r5] s t
  refine WP.mono (wp_countdown (body := .block ([.stb .r0 .r4 0, .addi .r4 .r4 1] ++
      ([.subi .r5 .r5 1] : List Instr)))
    (cnt := .r5) (N := k) (by omega_arith) (by omega_arith) Inv (fun j hj t ⟨t4, t0, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [b4]; simp [off], b0, by rw [m2]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k2⟩ b5) fun t ⟨_, _, tout, tb, tk⟩ => ⟨⟨tb, tout⟩, tk⟩
  obtain hst : WP isa (.block [.stb .r0 .r4 0, .addi .r4 .r4 1, .subi .r5 .r5 1]) t fun t' =>
      t' = (({ t with mem := t.mem.write (off O j) 1 ((BitVec.ofNat 64 0).setWidth 8) } :
          State).write .r4 (off O (j + 1))).write .r5 (t.gpr .r5 - BitVec.ofNat 64 1) := by
    prun [t4, t0, exec_stb (show Reg.r4 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      (ho.congr tk.wr).st (d := j) (n := 1) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  obtain hw1 := write1_outside t.mem O (d := j) ((BitVec.ofNat 64 0).setWidth 8) (by omega_arith)
  refine ⟨⟨by gsimp, by gsimp; exact t0, ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans (hw1.mono (by omega_arith) (by omega_arith))
  · intro i hi
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hw1 _ (by rw [ofs_off0 O (by omega_arith)]; omega_arith)]; exact tb i hi
    · rw [write1_self]; rfl
  · exact tk.trans' (((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end


/-!
# An FFDH parameter candidate on PPC64LE: the front

`front_ok`: the entry and `out` zeroed give `St` for the arguments
(`ppOf`), with `used` at `out_len`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE

/-- The candidate's arguments, on entry. -/
def ppOf (s : State) : PP where
  B := s.gpr .r10
  n := (stackArg s 0).toNat
  op := s.gpr .r3
  up := s.gpr .r5
  bits := (s.gpr .r6).toNat
  g := ((s.gpr .r7).setWidth 32).toNat
  rp := s.gpr .r8
  r := pcRand s
  sp := s.sp
  sv i := if i < 18 then s.gpr (Impl.Ffdh.PPC64LE.ParameterCandidate.saved i) else s.lr
  toc := s.gpr .r2

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

theorem zext_eq (x : BitVec 64) : (x.setWidth 32).setWidth 64 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq; simp

/-- Memory kept outside a region. -/
theorem out_word {O B : Addr} {L Z : Nat} {m m' : Mem} (hd : (⟨O, L⟩ : Region).Disjoint ⟨B, Z⟩)
    (hm : Outside O 0 L m m') (hnw : B.toNat + Z ≤ 2 ^ 64) {d : Nat} (hdz : d + 8 ≤ Z) :
    m'.readW (B + BitVec.ofNat 64 d) 64 = m.readW (B + BitVec.ofNat 64 d) 64 := by
  refine Mem.readW_congr fun i hi => hm _ (Or.inr ?_)
  by_contra hc
  exact hd (B + BitVec.ofNat 64 d + BitVec.ofNat 64 i) (by simp only [Region.Contains]; simp only [ofs] at hc; omega_arith)
    (by simp only [Region.Contains]; rw [VG.Offset.add_add, Mem.sub_ofNat_toNat B (by omega_arith)]; omega_arith)

theorem saved_notin : ∀ i < 18, Impl.Ffdh.PPC64LE.ParameterCandidate.saved i ∉ ([.r0, .r11, .r12] : List Reg) := by
  decide

theorem front_ok (s : State) (h : pcPre s) :
    WP isa (.seq (.block entry) zeroOut) s fun t =>
      St (ppOf s) t ∧ word t.mem (ppOf s).B 152 = BitVec.ofNat 64 (ppOf s).L ∧ t.lr = s.lr ∧
        Frame [⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩, ⟨s.gpr .r3, (s.gpr .r4).toNat⟩] s.mem t.mem ∧
        t.rd = s.rd := by
  obtain ⟨hsp, hspT, hrd, hwr, dOU, dOR, dOS, dOA, dUR, dUS, dUA, dRS, dSA, qO, qU, qR, qS, qA, nwO, nwU, nwR,
    nwS, hb1, hb2, hL, hg, hsw, -⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsw
  obtain hn : stackArg s 0 = BitVec.ofNat 64 (stackArg s 0).toNat := (ofNat_toNat _).symm
  obtain h8n : 160 ≤ 8 * (stackArg s 0).toNat := by omega_arith
  obtain hscr : Scr s (s.gpr .r10) (8 * (stackArg s 0).toNat) :=
    Scr.of_mem (by rw [hwr, Nat.mul_comm]; simp) (by omega_arith)
  obtain hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8 :=
    ⟨⟨stackArgAddr s 0, 8⟩, by rw [hrd]; simp, by simp [Region.Contains]⟩
  refine WP.seq ?_
  simp only [entry]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (entryA_ok rfl hn hargs h8n (hscr.st (by omega_arith))) fun tA ⟨⟨a11, a12, am⟩, ka⟩ => ?_
  refine WP.mono (saves_ok (s₀ := tA) a11 h8n (by omega_arith) fun i hi => by
    rw [ka.wr]; exact hscr.st (by omega_arith)) fun tS hS => ?_
  obtain hS10 : tS.gpr .r10 = s.gpr .r10 := by rw [hS.gpr, ka.gpr _ (by decide)]
  refine WP.mono (header_ok (s := tS) hS10 fun d hd => by
    rw [hS.wr, ka.wr]; exact hscr.st (d := d) (by omega_arith)) fun t₁ ⟨⟨c31, c7, cm⟩, kc⟩ => ?_
  obtain gS : ∀ r, r ∉ ([.r0, .r11, .r12] : List Reg) → tS.gpr r = s.gpr r := fun r hr => by
    rw [hS.gpr]; exact ka.gpr r hr
  obtain hS12 : tS.gpr .r12 = BitVec.ofNat 64 (stackArg s 0).toNat := by rw [hS.gpr]; exact a12
  obtain ⟨w0, w16, w24, w152, w32, w40, w128, w136, w144⟩ := hdrW_words tS.mem (s.gpr .r10) (tS.gpr .r12)
    (tS.gpr .r3) (tS.gpr .r4) (tS.gpr .r5) (tS.gpr .r6) (((tS.gpr .r7).setWidth 32).setWidth 64) (tS.gpr .r8)
    (tS.gpr .r9)
  rw [← cm] at w0 w16 w24 w152 w32 w40 w128 w136 w144
  obtain hwr₁ : t₁.wr = s.wr := by rw [kc.wr, hS.wr, ka.wr]
  obtain hscr₁ : Scr t₁ (s.gpr .r10) (8 * (stackArg s 0).toNat) := hscr.congr hwr₁
  obtain hout₁ : Scr t₁ (s.gpr .r3) (s.gpr .r4).toNat := (Scr.of_mem (by rw [hwr]; simp) nwO).congr hwr₁
  refine WP.mono (zeroOut_ok (s := t₁) hscr₁ hout₁ c31 (by rw [gS _ (by decide)] at w16; exact w16)
    (by rw [gS _ (by decide), ← ofNat_toNat (s.gpr .r4)] at w24; exact w24) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨⟨zb, zo⟩, kz⟩ => ?_
  have hnw := hscr.nowrap
  obtain dOS' : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩ := by
    rw [Nat.mul_comm]; exact dOS
  obtain wsW : ∀ d, d + 8 ≤ 8 * (stackArg s 0).toNat →
      t.mem.readW (s.gpr .r10 + BitVec.ofNat 64 d) 64 = t₁.mem.readW (s.gpr .r10 + BitVec.ofNat 64 d) 64 :=
    fun d hd => out_word dOS' zo hnw hd
  -- The memory, changed only in the working space and `out`.
  obtain fr : Frame [⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩, ⟨s.gpr .r3, (s.gpr .r4).toNat⟩] s.mem t.mem := by
    obtain ws_of : ∀ x, (∀ r ∈ ([⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩, ⟨s.gpr .r3, (s.gpr .r4).toNat⟩] : List Region),
        ¬ r.Contains x 1) → 8 * (stackArg s 0).toNat ≤ ofs (s.gpr .r10) x ∧ (s.gpr .r4).toNat ≤ ofs (s.gpr .r3) x :=
      fun x hx => by
        obtain h1 := hx _ (List.mem_cons_self ..)
        obtain h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        simp only [Region.Contains, ofs] at h1 h2 ⊢; omega_arith
    intro x hx
    obtain ⟨hx1, hx2⟩ := ws_of x hx
    rw [zo x (Or.inr (by omega_arith)), cm, hdrW_frm _ _ _ _ _ _ _ _ _ _ x (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (by omega_arith)), hS.out x (Or.inr (by omega_arith)), am]
    exact writeW_outside s.mem (s.gpr .r10) (d := 8 * (stackArg s 0).toNat - 160 + 144) s.lr (by omega_arith) x
      (Or.inr (by omega_arith))
  obtain hlen : (pcRand s).length = (s.gpr .r9).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  have hLe : (s.gpr .r4).toNat = (ppOf s).L := hL
  obtain kall : ∀ r, r ∉ ([.r0, .r4, .r5, .r7, .r11, .r12, .r31] : List Reg) → t.gpr r = s.gpr r := fun r hr => by
    rw [kz.gpr r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> simp)),
      kc.gpr r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> simp)),
      gS r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> simp))]
  obtain hd : ∀ {d}, d + 8 ≤ 256 → word t.mem (s.gpr .r10) d = word t₁.mem (s.gpr .r10) d := fun hd' =>
    wsW _ (by omega_arith)
  obtain sav : ∀ i < 19, word t.mem (s.gpr .r10) (8 * (stackArg s 0).toNat - saveBytes + 8 * i) = (ppOf s).sv i := by
    intro i hi
    simp only [saveBytes]
    rw [show word t.mem (s.gpr .r10) (8 * (stackArg s 0).toNat - 160 + 8 * i) =
        word t₁.mem (s.gpr .r10) (8 * (stackArg s 0).toNat - 160 + 8 * i) from wsW _ (by omega_arith), cm,
      (hdrW_frm _ _ _ _ _ _ _ _ _ _).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by omega_arith))
        (by omega_arith)]
    by_cases h18 : i < 18
    · rw [hS.saved i h18, ka.gpr _ (saved_notin i h18)]; simp [ppOf, h18]
    · obtain rfl : i = 18 := by omega_arith
      rw [hS.lrW]; simp only [word, off] at am ⊢
      rw [am, show 8 * (stackArg s 0).toNat - 160 + 8 * 18 = 8 * (stackArg s 0).toNat - 160 + 144 by omega_arith,
        VG.Proof.MillerRabin.PPC64LE.Search.rw_self]
      simp [ppOf]
  obtain dRS' : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩ := by
    rw [Nat.mul_comm]; exact dRS
  obtain dUS' : (⟨s.gpr .r5, 8⟩ : Region).Disjoint ⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩ := by
    rw [Nat.mul_comm]; exact dUS
  obtain hwrt : t.wr = s.wr := by rw [kz.wr, hwr₁]
  refine ⟨⟨hscr₁.congr kz.wr, (kz.gpr .r31 (by decide)).trans c31,
    ⟨(hd (d := 0) (by decide)).trans (w0.trans hS12),
     (hd (d := 16) (by decide)).trans (w16.trans (gS .r3 (by decide))),
     (hd (d := 24) (by decide)).trans (w24.trans ((gS .r4 (by decide)).trans (by rw [← hLe, ofNat_toNat]))),
     (hd (d := 32) (by decide)).trans (w32.trans (gS .r5 (by decide))),
     (hd (d := 40) (by decide)).trans (w40.trans ((gS .r6 (by decide)).trans (ofNat_toNat _).symm)),
     (hd (d := 128) (by decide)).trans (w128.trans (by rw [gS .r7 (by decide), zext_eq]; rfl)),
     (hd (d := 136) (by decide)).trans (w136.trans (gS .r8 (by decide))),
     (hd (d := 144) (by decide)).trans (w144.trans ((gS .r9 (by decide)).trans (by
       rw [show (ppOf s).r.length = (s.gpr .r9).toNat from hlen, ofNat_toNat])))⟩,
    ⟨fun i hi => ?_, fun i hi x hx he => ?_, ?_, ?_, ?_, fun x hx => ?_, ?_, fun x hx => ?_, by show (below s.sp 176).Disjoint ⟨s.gpr .r8, (pcRand s).length⟩; rw [hlen]; exact qR,
      by show (below s.sp 176).Disjoint ⟨s.gpr .r3, (ppOf s).L⟩; rw [← hLe]; exact qO, qU, by
      show (⟨s.gpr .r3, (ppOf s).L⟩ : Region).Disjoint _; rw [← hLe]; exact dOU⟩,
    ⟨hb1, hb2, hg, by simp only [ppOf, PP.L] at hLe ⊢; omega_arith, by simp only [ppOf]; omega_arith,
      by show (pcRand s).length < 2 ^ 64; rw [hlen]; exact (s.gpr .r9).isLt⟩,
    by rw [hwrt, hwr]; simp [ppOf, PP.Z, Nat.mul_comm], by rw [kz.sp, kc.sp, hS.sp, ka.sp]; rfl, hsp,
    by show (below s.sp 176).Disjoint ⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩; rw [Nat.mul_comm]; exact qS,
    sav, kall .r2 (by decide)⟩,
    (hd (d := 152) (by decide)).trans (w152.trans ((gS .r4 (by decide)).trans (by rw [← hLe, ofNat_toNat]))),
    by rw [kz.lr, kc.lr, hS.lr, ka.lr], fr, by rw [kz.rd, kc.rd, hS.rd, ka.rd]⟩
  · rw [kz.rd, kc.rd, hS.rd, ka.rd, hrd]
    rw [show (ppOf s).r.length = (s.gpr .r9).toNat from hlen] at hi
    exact ⟨⟨s.gpr .r8, (s.gpr .r9).toNat⟩, by simp, VG.Proof.Bignum.contains_byte _ hi (by omega_arith)⟩
  · rw [show (ppOf s).r.length = (s.gpr .r9).toNat from hlen] at hi
    subst he
    exact dRS' _ (VG.Proof.Bignum.contains_byte _ hi (by omega_arith)) (VG.Proof.Bignum.contains_scr hx)
  · show Spec.Rsa.bytesAt t.mem (s.gpr .r8) (pcRand s).length = pcRand s
    rw [hlen]
    refine VG.Proof.Rsa.rsa_bytes_frame fr (s.gpr .r9).isLt fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS'
    · exact dOR.symm
  · show Spec.Rsa.bytesAt t.mem (s.gpr .r3) (ppOf s).L = List.replicate (ppOf s).L 0
    rw [← hLe]; exact Pub.zero_bytes zb
  · show Scr t (s.gpr .r3) (ppOf s).L
    rw [← hLe]; exact hout₁.congr kz.wr
  · have hx' : ofs (s.gpr .r3) x < (s.gpr .r4).toNat := by rw [hLe]; exact hx
    exact VG.Proof.Bignum.out_scr dOS' (by simp only [Region.Contains]; simp only [ofs] at hx'; omega_arith)
  · exact (Scr.of_mem (by rw [hwr]; simp) nwU).congr hwrt
  · have hx' : ofs (s.gpr .r5) x < 8 := hx
    exact VG.Proof.Bignum.out_scr dUS' (by simp only [Region.Contains]; simp only [ofs] at hx'; omega_arith)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Exit`, which only this module used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: the exit

`exit_ok`: the link register and the nonvolatile registers back from the
save area, memory unchanged.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (ldh hWsLen)

theorem exitA_ok {p : PP} {t : State} (h : ESt p t) :
    WP isa (.block [ldh .r11 hWsLen, .lsl .r11 .r11 3, .add .r11 .r31 .r11, .subi .r11 .r11 saveBytes,
      .load .d .r0 .r11 144, .mtlr .r0]) t fun u =>
      u.gpr .r11 = off p.B (8 * p.n - 160) ∧ u.lr = p.sv 18 ∧ u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr ∧
        u.sp = t.sp ∧ ∀ r, r ≠ .r0 → r ≠ .r11 → u.gpr r = t.gpr r := by
  have hdn := h.dims.n
  have hb := h.dims.b1
  have hn' := h.dims.n'
  have hZe : p.Z = 8 * p.n := rfl
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  obtain h8n : 160 ≤ 8 * p.n := by omega_arith
  obtain e1 : p.B + BitVec.ofNat 64 (8 * p.n) - BitVec.ofNat 64 160 = off p.B (8 * p.n - 160) :=
    VG.Offset.add_ofNat_sub p.B h8n
  obtain l0 : InRegions (t.rd ++ t.wr) (p.B + BitVec.ofNat 64 0) 8 := h.scr.ld (d := 0) (by omega_arith)
  obtain l144 : InRegions (t.rd ++ t.wr) (off p.B (8 * p.n - 160 + 144)) 8 := h.scr.ld (by omega_arith)
  have w0 : t.mem.readW (p.B + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 p.n := h.len
  obtain w144 : t.mem.readW (off p.B (8 * p.n - 160 + 144)) 64 = p.sv 18 := h.save 18 (by decide)
  simp only [ldh, hWsLen, saveBytes]
  prun [exec_mtlr, h.r31, l0, w0, Pub.ofNat_shl3, e1, l144, w144]
  intro r h0 h11
  simp only [h0, h11, ↓reduceIte]

local notation "sv" => Impl.Ffdh.PPC64LE.ParameterCandidate.saved

theorem sv_inj : ∀ i < 18, ∀ j < 18, sv i = sv j → i = j := by decide

theorem sv_ne11 : ∀ i < 18, sv i ≠ .r11 := by decide

/-- The first `k` registers restored to `v`, from the state `sB`. -/
structure XI (sB : State) (S : Addr) (v : Nat → BitVec 64) (k : Nat) (s : State) : Prop where
  r11 : s.gpr .r11 = S
  restored : ∀ i < k, s.gpr (sv i) = v i
  others : ∀ r, (∀ i < 18, r ≠ sv i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp
  lr : s.lr = sB.lr

theorem restore_step (sB : State) {S : Addr} {v : Nat → BitVec 64}
    (hin : ∀ i < 18, InRegions (sB.rd ++ sB.wr) (off S (8 * i)) 8)
    (hv : ∀ i < 18, sB.mem.readW (off S (8 * i)) 64 = v i)
    {k : Nat} (hk : k < 18) {s : State} (h : XI sB S v k s) :
    WP isa (.block [.load .d (sv k) .r11 (8 * k)]) s (XI sB S v (k + 1)) := by
  obtain hin' : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [h.rd, h.wr, h.r11]; exact hin k hk
  obtain hv' : s.mem.readW (S + BitVec.ofNat 64 (8 * k)) 64 = v k := by rw [h.mem]; exact hv k hk
  obtain hn11 := sv_ne11 k hk
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r11 ≠ .r0 by decide) (show 8 * k < 2 ^ 15 ∧ (8 * k) % 4 = 0 by omega_arith) hin',
    Option.some.injEq, exists_eq_left', h.r11, hv']
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (Ne.symm hn11)]; exact h.r11
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : sv i ≠ sv k := fun e => absurd (sv_inj i (by omega_arith) k hk e) (by omega_arith)
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr k hk)]
    exact h.others r hr

/-- The exit: the registers and the link register back from the save area. -/
theorem exit_ok {p : PP} {t : State} (h : ESt p t) :
    WP isa (.block exit) t fun u =>
      (∀ i < 18, u.gpr (sv i) = p.sv i) ∧ u.lr = p.sv 18 ∧ u.mem = t.mem ∧ u.sp = t.sp ∧
        ∀ r, r ≠ .r0 → r ≠ .r11 → (∀ i < 18, r ≠ sv i) → u.gpr r = t.gpr r := by
  have hdn := h.dims.n
  have hb := h.dims.b1
  have hn' := h.dims.n'
  have hZe : p.Z = 8 * p.n := rfl
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  unfold exit
  rw [map_flatMap, WP.block_append_iff]
  refine WP.mono (exitA_ok h) fun sB ⟨b11, blr, bm, brd, bwr, bsp, bo⟩ => ?_
  obtain hin : ∀ i < 18, InRegions (sB.rd ++ sB.wr) (off (off p.B (8 * p.n - 160)) (8 * i)) 8 := fun i hi => by
    rw [brd, bwr, show off (off p.B (8 * p.n - 160)) (8 * i) = off p.B (8 * p.n - 160 + 8 * i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact h.scr.ld (by omega_arith)
  obtain hv : ∀ i < 18, sB.mem.readW (off (off p.B (8 * p.n - 160)) (8 * i)) 64 = p.sv i := fun i hi => by
    rw [bm, show off (off p.B (8 * p.n - 160)) (8 * i) = off p.B (8 * p.n - 160 + 8 * i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact h.save i (by omega_arith)
  refine WP.mono (wp_range_flatMap (M := isa) (XI sB (off p.B (8 * p.n - 160)) p.sv)
    (fun k s hk hs => restore_step sB hin hv hk hs) 18 (Nat.le_refl _) sB
    ⟨b11, fun _ h => absurd h (by omega_arith), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩) fun u hu => ?_
  exact ⟨hu.restored, by rw [hu.lr, blr], by rw [hu.mem, bm], by rw [hu.sp, bsp],
    fun r h0 h11 hs => by rw [hu.others r hs, bo r h0 h11]⟩

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end


/-!
# An FFDH parameter candidate on PPC64LE: correctness

`code_correct`: `code` meets `pcContract`'s postcondition and keeps what the
calling convention preserves, for any implementation of the round.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
theorem sieved_short {bits g : Nat} {r : List Byte} (h : r.length < (bits + 7) / 8) :
    Spec.Ffdh.sievedParameterCandidate bits g r = none := by
  have : (r.take ((bits + 7) / 8)).length ≠ (bits + 7) / 8 := by rw [List.length_take]; omega_using [h]
  simp only [Spec.Ffdh.sievedParameterCandidate, Spec.RsaKeyGen.draw, this, ↓reduceIte, bind, Option.bind]

/-- The tape's length and `out_len`. -/
theorem lenLoad_ok {p : PP} {t : State} (h : St p t) :
    WP isa (.block [ldh .r3 hRandLen, ldh .r4 hLen]) t fun u => (u.gpr .r3 = BitVec.ofNat 64 p.r.length ∧
      u.gpr .r4 = BitVec.ofNat 64 p.L ∧ u.mem = t.mem) ∧ Keep [.r3, .r4] t u := by
  refine WP.keep [.r3, .r4] ?_ (by decide)
  simp only [ldh, hRandLen, hLen]
  prun [h.r31, h.ld (d := 144) (by decide), h.ld (d := 24) (by decide), h.args.rlen', h.args.len']

/-- The length check's flag. -/
theorem lenChk_ok {p : PP} {t : State} (h : St p t) (hU : word t.mem p.B 152 = BitVec.ofNat 64 p.L) :
    WP isa (.block (([ldh .r3 hRandLen, ldh .r4 hLen] : List Instr) ++ geFlag .r5 .r3 .r4)) t fun v =>
      isa.eval (.zero .d .r5) v = some (decide ((if p.L ≤ p.r.length then 1 else 0) = 0)) ∧ St p v ∧
        word v.mem p.B 152 = BitVec.ofNat 64 p.L ∧ v.mem = t.mem ∧ v.rd = t.rd := by
  have hrl := h.dims.rl
  have hb2 := h.dims.b2
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  rw [WP.block_append_iff]
  refine WP.mono (lenLoad_ok h) fun u ⟨⟨a3, a4, am⟩, ka⟩ => ?_
  refine WP.mono (geFlag_ok a3 a4 hrl (by omega_using [hb2, hLe])) fun v ⟨⟨a5, vm⟩, kv⟩ => ?_
  obtain hm : v.mem = t.mem := vm.trans am
  exact ⟨eval_zero_ofNat v .r5 (by split <;> decide) a5, h.step (by rw [hm]; exact Frm.refl _ _ _) (ka.trans kv),
    by rw [hm]; exact hU, hm, (ka.trans kv).rd⟩

/-- The length check, then `main` or the status 0. -/
theorem body_ok (R : RoundImpl) {p : PP} {T : Addr} {t : State} (h : St p t) (ht : TabIn p.B p.Z T t)
    (hU : word t.mem p.B 152 = BitVec.ofNat 64 p.L) :
    WP isa (.seq (.block (([ldh .r3 hRandLen, ldh .r4 hLen] : List Instr) ++ geFlag .r5 .r3 .r4))
      (.ite (.zero .d .r5) (.block (finish 0)) (main R.name R.code))) t
      (CEnd p (Spec.Ffdh.sievedParameterCandidate p.bits p.g p.r)) := by
  refine WP.seq (WP.mono_syms (lenChk_ok h hU) fun v ⟨he, st, hUv, vm, vrd⟩ sy => ?_)
  refine WP.ite (decide ((if p.L ≤ p.r.length then 1 else 0) = 0)) he (fun hb => ?_) (fun hb => ?_)
  · have hs : p.r.length < p.L := by
      by_contra hc; simp only [decide_eq_true_eq] at hb; rw [ite_eq_left (by omega_using [hc])] at hb; exact absurd hb (by decide)
    rw [sieved_short (by omega)]
    exact finEnd st (r := 0) (Or.inl rfl) rfl rfl rfl hUv
  · have hl : p.L ≤ p.r.length := by
      by_contra hc; simp only [decide_eq_false_iff_not] at hb; exact hb (by rw [ite_eq_right (by omega_using [hc])])
    exact main_ok R st (ht.step sy (rs := []) (by rw [vm]; exact Frm.refl _ _ _) (by simp) vrd) hUv hl

theorem preserved_cases : ∀ r ∈ preserved,
    r = .r2 ∨ ∃ i < 18, Impl.Ffdh.PPC64LE.ParameterCandidate.saved i = r := by decide

theorem r2_cases : ∀ i < 18, Reg.r2 ≠ Impl.Ffdh.PPC64LE.ParameterCandidate.saved i := by decide

theorem r3_cases : ∀ i < 18, Reg.r3 ≠ Impl.Ffdh.PPC64LE.ParameterCandidate.saved i := by decide

theorem small_setWidth {k : Nat} (hk : k < 2 ^ 32) : ((BitVec.ofNat 64 k).setWidth 32).toNat = k := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hk]

theorem status_le (res : Option (Option Nat × Spec.RsaKeyGen.Rand)) : Proof.Ffdh.candidateStatus res ≤ 2 := by
  rcases res with _ | ⟨_ | _, _⟩ <;> simp [Proof.Ffdh.candidateStatus]

/-- The front, and the table where the state names it. -/
theorem front_tab (s : State) (h : pcPre s) :
    WP isa (.seq (.block entry) zeroOut) s fun t => St (ppOf s) t ∧
      word t.mem (ppOf s).B 152 = BitVec.ofNat 64 (ppOf s).L ∧
      TabIn (ppOf s).B (ppOf s).Z (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) t := by
  have hpre := h
  obtain ⟨-, -, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htab⟩ := h
  refine WP.mono_syms (front_ok s hpre) fun t ⟨st, hU, _, fr, trd⟩ sy => ⟨st, hU, ?_⟩
  obtain ⟨tfit, tat, tdO, tdS⟩ := htab
  refine ⟨by rw [sy], fun i hi => ?_, by rw [trd, hrd]; simp, tfit, ?_⟩
  · rw [fr.readW (r := tabR s) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [Nat.mul_comm]; exact tdS
      · exact tdO) (by decide)]
    exact tat i hi
  · show (tabR s).Disjoint ⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩
    rw [Nat.mul_comm]; exact tdS

/-- `vg_ffdh_parameter_candidate_sieved`, for any implementation of the round. -/
theorem code_correct (R : RoundImpl) (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa (code R.name R.code) s tr t ∧ abiPreserved s t ∧ pcContract.post s t := by
  show WP isa (code R.name R.code) s fun t => abiPreserved s t ∧ pcPost s t
  have hpre := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -, -⟩ := h
  have hLe : (s.gpr .r4).toNat = (ppOf s).L := hL
  obtain hlen : (ppOf s).r.length = (s.gpr .r9).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  unfold code
  refine wp_then (front_tab s hpre) fun t ⟨st, hU, ht⟩ => ?_
  refine wp_then (body_ok R st ht hU) fun u hu => ?_
  obtain ⟨E, u3, uo, uu⟩ := hu
  refine WP.mono (exit_ok E) fun w ⟨wr, wlr, wm, wsp, wo⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rcases preserved_cases r hr with rfl | ⟨i, hi, rfl⟩
    · rw [wo .r2 (by decide) (by decide) r2_cases, E.r2]; rfl
    · rw [wr i hi]; simp [ppOf, hi]
  · rw [wsp, E.sp]; rfl
  · rw [wlr]; simp [ppOf]
  · have hres : pcResult s = Spec.Ffdh.sievedParameterCandidate (ppOf s).bits (ppOf s).g (ppOf s).r := rfl
    simp only [pcPost]
    rw [hres, wm, wo .r3 (by decide) (by decide) r3_cases, u3, hLe]
    refine ⟨small_setWidth (by have := status_le (Spec.Ffdh.sievedParameterCandidate (ppOf s).bits (ppOf s).g (ppOf s).r); omega_using [this]),
      ?_, ?_⟩
    · refine uo.trans ?_
      generalize Spec.Ffdh.sievedParameterCandidate (ppOf s).bits (ppOf s).g (ppOf s).r = res
      rcases res with _ | ⟨_ | _, _⟩ <;> rfl
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
      refine congrArg (· :: []) (uu.trans ?_)
      rw [← hlen]
      generalize Spec.Ffdh.sievedParameterCandidate (ppOf s).bits (ppOf s).g (ppOf s).r = res
      rcases res with _ | ⟨_ | _, _⟩ <;> rfl

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-! ### `Ffdh.PPC64LE.ParameterCandidate.CTMain`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.ParameterCandidate.CTTests`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.ParameterCandidate.CTRes`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.ParameterCandidate.CTTest`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.ParameterCandidate.CTMr`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.ParameterCandidate.CTDraw`, which only this module used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: a draw in constant time

Two runs draw the same witness from the same tape (`DI`), whatever the
registers saved on entry: `PP.with` gives the public data `q` the saved
registers of one run. The head pins the tape's address and the count it
loads; the pieces up to the range check are then checked by the taint
analysis; the branches are on the witness's range and its round's result,
which `q` decides.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl arr)
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)

/-- `p`'s public data with a run's saved registers and `r2`. -/
def PP.with (p : PP) (sv : Nat → BitVec 64) (toc : BitVec 64) : PP := { p with sv := sv, toc := toc }

/-- A draw's public data. -/
structure DrawD where
  q : PP
  mb : Nat
  N : Nat
  u : Nat
  i : Nat
  K : Nat

/-- Before a draw. -/
def DI (d : DrawD) (s : State) : Prop :=
  ∃ sv toc, MSt (d.q.with sv toc) d.mb d.N d.K s ∧ word s.mem d.q.B 152 = BitVec.ofNat 64 d.u ∧
    d.u + (d.mb + 7) / 8 ≤ d.q.r.length ∧ word s.mem d.q.B 176 = BitVec.ofNat 64 d.i ∧
    word s.mem d.q.B 160 = BitVec.ofNat 64 4 ∧ d.i < 2 ^ 62

theorem pins_DI : Pins DI [.r29, .r31] := by
  rintro d s₁ s₂ ⟨_, _, h₁, -⟩ ⟨_, _, h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.ph.r29, h₂.ph.r29]
  · rw [h₁.st.r31, h₂.st.r31]; rfl

/-- After a draw's head. -/
def DA (d : DrawD) (t : State) : Prop :=
  ∃ sv toc s, (MSt (d.q.with sv toc) d.mb d.N d.K s ∧ word s.mem d.q.B 152 = BitVec.ofNat 64 d.u ∧
    d.u + (d.mb + 7) / 8 ≤ d.q.r.length ∧ word s.mem d.q.B 176 = BitVec.ofNat 64 d.i ∧
    word s.mem d.q.B 160 = BitVec.ofNat 64 4 ∧ d.i < 2 ^ 62) ∧ DHead (d.q.with sv toc) d.mb d.u s t

theorem pins_DA : Pins DA [.r6, .r10, .r11, .r12, .r29, .r31] := by
  rintro d s₁ s₂ ⟨_, _, _, ⟨M₁, -⟩, ⟨a12, a6, a10, -⟩, k₁⟩ ⟨_, _, _, ⟨M₂, -⟩, ⟨b12, b6, b10, -⟩, k₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a6, b6]
  · rw [a10, b10]; rfl
  · rw [k₁.gpr _ (by decide), k₂.gpr _ (by decide), M₁.ph.r11, M₂.ph.r11]
  · rw [a12, b12]; rfl
  · rw [k₁.gpr _ (by decide), k₂.gpr _ (by decide), M₁.ph.r29, M₂.ph.r29]
  · rw [k₁.gpr _ (by decide), k₂.gpr _ (by decide), M₁.st.r31, M₂.st.r31]; rfl

theorem drawHead_ct : RelCT isa (Two DI) (.block ([ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK,
    .add .r3 .r3 .r6, sth .r3 hUsed] ++ base .r10 4)) (Two DA) :=
  two_post (two_taint _ pins_DI (by taint_decide)) fun _ s ⟨sv, toc, M, hu, hroom, hI, hS, hi⟩ =>
    WP.mono (dHead_ok ⟨M.st, M.ph, M.prep, hu, hroom, M.mb1, M.mb2⟩) fun t ht =>
      ⟨sv, toc, s, ⟨M, hu, hroom, hI, hS, hi⟩, ht⟩

/-- Before a draw's branches. -/
def DMd (d : DrawD) (t : State) : Prop := ∃ sv toc, DMid (d.q.with sv toc) d.mb d.N d.u d.i d.K t ∧ d.i < 2 ^ 62

theorem drawMid_ct : RelCT isa (Two DA) (Prog.chain drawMid (.block [])) (Two DMd) :=
  two_post (two_taint _ pins_DA (by taint_decide)) fun _ _ ⟨sv, toc, _, ⟨M, hu, hroom, hI, hS, hi⟩, ht⟩ =>
    WP.mono (drawRest_ok M hu hroom hI hS ht) fun _ h' => ⟨sv, toc, h', hi⟩

theorem beq_zero_of_iff {x : BitVec 64} {P : Prop} [Decidable P] (h : x = 0#64 ↔ P) : (x == 0) = decide P := by
  apply Bool.eq_iff_iff.mpr; rw [beq_iff_eq, decide_eq_true_iff]; exact h

theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

/-- The round's call, from a witness in range. -/
def rcOf (d : DrawD) : RcD := ⟨d.q.B, d.q.n, wOf d.mb, d.N, wA d.mb d.q.r d.u⟩

/-- After the round. -/
def DR (d : DrawD) (t : State) : Prop :=
  t.gpr .r3 = BitVec.ofNat 64 (if Proof.MillerRabin.Round.round d.N (wA d.mb d.q.r d.u) then 1 else 0) ∧ t.gpr .r31 = d.q.B

theorem pins_DR : Pins DR [.r31] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁, h₂]

theorem round_ct (R : RoundImpl) : RelCT isa (Two fun d s => (DMd d s ∧ decide (wA d.mb d.q.r d.u < 2) = false) ∧
    decide (¬ wA d.mb d.q.r d.u < d.N - 1) = false) (round R.name R.code) fun _ _ => True := by
  have hrc : ∀ d s, ((DMd d s ∧ decide (wA d.mb d.q.r d.u < 2) = false) ∧
      decide (¬ wA d.mb d.q.r d.u < d.N - 1) = false) → RC (rcOf d) s := by
    rintro d s ⟨⟨⟨sv, toc, h, _⟩, h2⟩, hN⟩
    simp only [decide_eq_false_iff_not, Decidable.not_not] at h2 hN
    have hsp := h.m.st.sp
    exact ⟨h.m.prep, h.a4, show wA d.mb d.q.r d.u < d.N by omega_using [hN], by rw [hsp]; exact h.m.st.stk, by rw [hsp]; exact h.m.st.stkB⟩
  unfold Impl.MillerRabin.PPC64LE.Search.round
  refine RelCT.seq (two_post (two_map rcOf hrc (roundCall_ct R)) (Ψ := DR) fun d s h => ?_) ?_
  · obtain ⟨hp, ha, hac, hsp, hstk⟩ := hrc d s h
    exact WP.mono (roundCall_ok R hp ha hac hsp hstk) fun t ht => ⟨ht.r3, ht.prep.env.h31⟩
  refine two_ite' (fun d => !Proof.MillerRabin.Round.round d.N (wA d.mb d.q.r d.u)) (fun d s h => ?_)
    (two_taint _ (fun d s₁ s₂ h₁ h₂ => pins_DR d s₁ s₂ h₁.1 h₂.1) (by taint_decide))
    (two_taint _ (fun d s₁ s₂ h₁ h₂ => pins_DR d s₁ s₂ h₁.1 h₂.1) (by taint_decide))
  rw [eval_zero, h.1]
  cases Proof.MillerRabin.Round.round d.N (wA d.mb d.q.r d.u) <;> rfl

theorem drawBranch_ct (R : RoundImpl) : RelCT isa (Two DMd) (drawBranch R.name R.code) fun _ _ => True := by
  unfold drawBranch
  refine two_ite' (fun d => decide (wA d.mb d.q.r d.u < 2)) (fun d s ⟨sv, toc, h, _⟩ => by
      rw [eval_zero, beq_zero_of_iff h.z24]; rfl)
    (two_taint _ (pins_nil _) (by taint_decide)) ?_
  refine two_ite' (fun d => decide (¬ wA d.mb d.q.r d.u < d.N - 1)) (fun d s ⟨⟨sv, toc, h, _⟩, _⟩ => by
      rw [eval_zero, beq_zero_of_iff h.z20]; rfl)
    (two_taint _ (pins_nil _) (by taint_decide)) (round_ct R)

/-- A draw leaks the same from the same public data. -/
theorem draw_ct (R : RoundImpl) : RelCT isa (Two DI) (draw R.name R.code) fun _ _ => True := by
  rw [draw_eq]
  exact RelCT.seq drawHead_ct (RelCT.chain (RelCT.seq drawMid_ct (drawBranch_ct R)))

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on PPC64LE: the witnesses in constant time

`millerRabin_ct`: two runs testing the same modulus from the same tape
(`MI0`) leak the same: whether there is room for a witness, the draw
(`draw_ct`), and whether the loop goes on (`mrGo`), each decided by the
public data, the next iteration's data a function of it (`mrNext`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

/-- The witness loop's public data. -/
structure MrD where
  q : PP
  mb : Nat
  N : Nat
  res : Option (Bool × List Byte)
  i : Nat
  u : Nat
  K : Nat

/-- At the head of the witness loop. -/
def MI (a : MrD) (s : State) : Prop :=
  (∃ sv toc, MrSt (a.q.with sv toc) a.mb a.N a.K a.res a.i a.u s) ∧ Spec.RsaKeyGen.bitLength (a.N - 1) = a.mb

/-- After the loop. -/
def ME (a : MrD) (s : State) : Prop := ∃ sv toc, MrEnd (a.q.with sv toc) a.mb a.N a.K a.res s

def mrNext (a : MrD) : MrD :=
  { a with i := dIdx a.N a.i (wA a.mb a.q.r a.u), u := a.u + (a.mb + 7) / 8 }

/-- The working space's address. -/
def R31 (a : MrD) (s : State) : Prop := s.gpr .r31 = a.q.B

theorem pins_R31 : Pins R31 [.r31] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁, h₂]

theorem pins_MI : Pins MI [.r31] := by
  rintro d s₁ s₂ ⟨⟨_, _, h₁⟩, -⟩ ⟨⟨_, _, h₂⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.m.st.r31, h₂.m.st.r31]; rfl

/-- After the head's block. -/
def MH (a : MrD) (s : State) : Prop :=
  MI a s ∧ s.gpr .r5 = BitVec.ofNat 64 (if (a.mb + 7) / 8 ≤ a.q.r.length - a.u then 1 else 0)

theorem headBlk_MH {a : MrD} {s : State} (h : MI a s) :
    WP isa (.block (([ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] : List Instr) ++
      geFlag .r5 .r3 .r4)) s (MH a) := by
  obtain ⟨⟨sv, toc, hs⟩, hbl⟩ := h
  refine WP.mono (mrHeadBlk_ok hs) fun t ⟨⟨t5, tm⟩, k⟩ => ⟨⟨⟨sv, toc, ?_⟩, hbl⟩, t5⟩
  have M : MSt (a.q.with sv toc) a.mb a.N a.K t := hs.m.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k
    (by decide) (k.gpr _ (by decide)) (k.gpr _ (by decide)) (k.gpr _ (by decide))
  exact ⟨M, by rw [tm]; exact hs.used, by rw [tm]; exact hs.idx, by rw [tm]; exact hs.stat, hs.ul, hs.ik, hs.rest⟩

theorem mrBody_ct (R : RoundImpl) : RelCT isa (Two MI)
    (.seq (.block (([ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] : List Instr) ++
        geFlag .r5 .r3 .r4))
      (.seq (.ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat]) (draw R.name R.code))
        (.block [ldh .r3 hStat, .subi .r3 .r3 4]))) fun _ _ => True := by
  refine RelCT.seq (two_post (two_taint _ pins_MI (by taint_decide)) fun _ _ h => headBlk_MH h)
    (RelCT.seq (R := Two R31) ?_ ?_)
  rotate_left
  · exact two_taint _ pins_R31 (by taint_decide)
  have ev : ∀ a s, MH a s → isa.eval (.zero .d .r5) s = some (!decide ((a.mb + 7) / 8 ≤ a.q.r.length - a.u)) :=
    fun a s h => by
      rw [eval_zero_ofNat s .r5 (by split <;> decide) h.2]
      split <;> simp_all
  refine two_ite' (fun a => !decide ((a.mb + 7) / 8 ≤ a.q.r.length - a.u)) ev ?_ ?_
  · refine two_post (two_taint _ (fun a s₁ s₂ h₁ h₂ => pins_MI a s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide))
      fun a s h => ?_
    obtain ⟨⟨⟨⟨sv, toc, hs⟩, -⟩, -⟩, -⟩ := h
    have l160 := hs.m.st.st (d := 160) (by decide)
    refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r31 = a.q.B) ?_ (by decide)) fun t ⟨ht, _⟩ => ht
    simp only [sth, hStat]; prun [hs.m.st.r31, l160]; rfl
  · have hd : ∀ a s, MH a s ∧ (!decide ((a.mb + 7) / 8 ≤ a.q.r.length - a.u)) = false →
        DI ⟨a.q, a.mb, a.N, a.u, a.i, a.K⟩ s := by
      rintro a s ⟨⟨⟨⟨sv, toc, hs⟩, -⟩, -⟩, hb⟩
      simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
      have hul : a.u ≤ a.q.r.length := hs.ul
      have hik : a.i < a.K := hs.ik
      have hK : a.K ≤ 128 := hs.m.ph.k2
      exact ⟨sv, toc, hs.m, hs.used, show a.u + (a.mb + 7) / 8 ≤ a.q.r.length by omega_using [hb, hul], hs.idx, hs.stat,
        show a.i < 2 ^ 62 by omega_using [hik, hK]⟩
    refine two_post (two_map (fun a : MrD => (⟨a.q, a.mb, a.N, a.u, a.i, a.K⟩ : DrawD)) hd (draw_ct R)) fun a s h => ?_
    obtain ⟨sv, toc, M, hu, hroom, hI, hS, hi⟩ := hd a s h
    exact WP.mono (draw_ok R M hu hroom hI hS hi) fun t ht => ht.1.st.r31

/-- Before the witness loop. -/
def MI0 (a : MrD) (s : State) : Prop :=
  (∃ sv toc, MSt (a.q.with sv toc) a.mb a.N a.K s ∧ word s.mem a.q.B 152 = BitVec.ofNat 64 a.u) ∧
    a.u ≤ a.q.r.length ∧ a.i = 0 ∧ a.res = checkWitnesses a.N (a.K) (a.q.r.drop a.u) ∧
    Spec.RsaKeyGen.bitLength (a.N - 1) = a.mb

theorem pins_MI0 : Pins MI0 [.r31] := by
  rintro d s₁ s₂ ⟨⟨_, _, h₁, -⟩, -⟩ ⟨⟨_, _, h₂, -⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.st.r31, h₂.st.r31]; rfl

/-- The witness loop leaks the same in runs testing the same modulus from the
same tape. -/
theorem millerRabin_ct (R : RoundImpl) : RelCT isa (Two MI0) (millerRabin R.name R.code) (Two ME) := by
  unfold millerRabin
  refine RelCT.seq (two_post (two_taint _ pins_MI0 (by taint_decide)) (Ψ := MI) fun a s h => ?_)
    (two_loopD (fun a => a.q.r.length + 1 - a.u) mrNext (fun a => mrGo a.q.r a.mb a.N a.i a.u a.K) (mrBody_ct R)
      fun a s h => ?_)
  · obtain ⟨⟨sv, toc, M, hu⟩, hul, hi, hres, hbl⟩ := h
    refine WP.mono (mrInit_ok M hu hul) fun t ht => ⟨⟨sv, toc, ?_⟩, hbl⟩
    rw [hi, hres]; exact ht
  · obtain ⟨⟨sv, toc, hs⟩, hbl⟩ := h
    have hm1 := hs.m.mb1
    refine WP.mono (mrIter_ok R hbl hs) fun t ⟨he, hend, hgo⟩ =>
      ⟨he, fun hg => ⟨sv, toc, hend hg⟩, fun hg => ⟨?_, ⟨sv, toc, hgo hg⟩, hbl⟩⟩
    have hul : a.u + (a.mb + 7) / 8 ≤ a.q.r.length := (hgo hg).ul
    show a.q.r.length + 1 - (a.u + (a.mb + 7) / 8) < a.q.r.length + 1 - a.u
    omega_using [hm1, hul]

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on PPC64LE: a test in constant time

A modulus's working space (`phase`) depends on the public bit length alone;
the loop of `topMask` counts down from a number it fixes, pinned once its
first block has computed it. p's shape loads the tape's address and length
from the header, pinned once loaded. The Montgomery set-up runs on the
working space's addresses, then the witnesses as in `millerRabin_ct`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

/-- The candidate's state, whatever the registers saved on entry. -/
def PS (q : PP) (s : State) : Prop := ∃ sv toc, St (q.with sv toc) s

theorem pins_PS : Pins PS [.r31] := by
  rintro q s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.r31, h₂.r31]; rfl

/-- After `phase b`'s head: the bit length and words in the header. -/
def PH1 (b : Bool) (q : PP) (s : State) : Prop :=
  ∃ sv toc, St (q.with sv toc) s ∧ word s.mem q.B (8 * hMb) = BitVec.ofNat 64 (mbOf q b) ∧
    word s.mem q.B (8 * hW) = BitVec.ofNat 64 (wOf (mbOf q b))

theorem pins_PH1 (b : Bool) : Pins (PH1 b) [.r31] := by
  rintro q s₁ s₂ ⟨_, _, h₁, -⟩ ⟨_, _, h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.r31, h₂.r31]; rfl

/-- After `topMask`'s first block: its count. -/
def PT (b : Bool) (q : PP) (s : State) : Prop :=
  s.gpr .r31 = q.B ∧ s.gpr .r3 = BitVec.ofNat 64 (mbOf q b + 64 - 64 * wOf (mbOf q b))

theorem pins_PT (b : Bool) : Pins (PT b) [.r3, .r31] := by
  rintro q s₁ s₂ ⟨a31, a3⟩ ⟨b31, b3⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a3, b3]
  · rw [a31, b31]

theorem phaseHead_ct (b : Bool) : RelCT isa (Two PS) (.block (phaseHead b)) fun _ _ => True := by
  cases b
  · exact two_taint _ pins_PS (by taint_decide)
  · exact two_taint _ pins_PS (by taint_decide)

theorem phase_ct (b : Bool) : RelCT isa (Two PS) (phase b) fun _ _ => True := by
  unfold phase topMask
  refine RelCT.seq (two_post (phaseHead_ct b) (Ψ := PH1 b) fun q s ⟨sv, toc, h⟩ => ?_)
    (RelCT.seq (two_post (two_taint _ (pins_PH1 b) (by taint_decide)) (Ψ := PT b)
      fun q s ⟨sv, toc, h, hm, hw⟩ => ?_) (two_taint _ (pins_PT b) (by taint_decide)))
  · exact WP.mono (phaseHead_ok h b) fun u ⟨⟨_, _, _, um, _, uw, _, _, _, uf⟩, ku⟩ =>
      ⟨sv, toc, h.step (Frm.toMut (uf.mono fun r hr => List.mem_append_left _ hr) (phRanges_mut _)) ku, um, uw⟩
  · exact WP.mono (topT1_ok h hm hw) fun u ⟨⟨u3, _, _⟩, ku⟩ => ⟨(ku.gpr .r31 (by decide)).trans h.r31, u3⟩

/-- In a modulus's working space. -/
def PA (b : Bool) (q : PP) (s : State) : Prop := ∃ sv toc C, St (q.with sv toc) s ∧ Ph (q.with sv toc) (mbOf q b) C s

theorem pins_PA (b : Bool) : Pins (PA b) [.r10, .r11, .r29, .r31] := by
  rintro q s₁ s₂ ⟨_, _, _, h₁, p₁⟩ ⟨_, _, _, h₂, p₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [p₁.r10, p₂.r10]; rfl
  · rw [p₁.r11, p₂.r11]
  · rw [p₁.r29, p₂.r29]
  · rw [h₁.r31, h₂.r31]; rfl

/-- After `shapeP`'s first block. -/
def SH1 (q : PP) (s : State) : Prop :=
  s.gpr .r31 = q.B ∧ s.gpr .r10 = off q.B (slot (wOf q.bits) 0) ∧ s.gpr .r11 = BitVec.ofNat 64 (2 * wOf q.bits) ∧
    s.gpr .r12 = off q.rp 0 ∧ s.gpr .r6 = BitVec.ofNat 64 q.L

theorem pins_SH1 : Pins SH1 [.r6, .r10, .r11, .r12, .r31] := by
  rintro q s₁ s₂ ⟨a31, a10, a11, a12, a6⟩ ⟨b31, b10, b11, b12, b6⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a6, b6]
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a12, b12]
  · rw [a31, b31]

theorem shapeP_ct : RelCT isa (Two (PA false)) shapeP fun _ _ => True := by
  unfold shapeP
  refine RelCT.seq (two_post (two_taint _ (pins_PA false) (by taint_decide)) (Ψ := SH1) fun q s ⟨sv, toc, _, h, hp⟩ =>
    WP.mono (shapeHead_ok h) fun u ⟨⟨u12, u6, _⟩, ku⟩ => ⟨(ku.gpr .r31 (by decide)).trans h.r31,
      (ku.gpr .r10 (by decide)).trans hp.r10, (ku.gpr .r11 (by decide)).trans hp.r11, u12, u6⟩)
    (two_taint _ pins_SH1 (by taint_decide))

theorem phasePA_ct (b : Bool) : RelCT isa (Two PS) (phase b) (Two (PA b)) :=
  two_post (phase_ct b) fun _ _ ⟨sv, toc, h⟩ => WP.mono (phase_ok h b) fun _ ⟨⟨ht, hp, _⟩, _⟩ => ⟨sv, toc, _, ht, hp⟩

/-- A test's public data, once its modulus is in place. -/
structure TD where
  q : PP
  mb : Nat
  N : Nat
  u : Nat
  K : Nat

/-- Before a test's Montgomery set-up. -/
def TC (d : TD) (s : State) : Prop := ∃ sv toc, TCPre (d.q.with sv toc) d.mb d.N d.u d.K s

theorem pins_TC : Pins TC [.r10, .r11, .r29, .r31] := by
  rintro d s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.ph.r10, h₂.ph.r10]; rfl
  · rw [h₁.ph.r11, h₂.ph.r11]
  · rw [h₁.ph.r29, h₂.ph.r29]
  · rw [h₁.st.r31, h₂.st.r31]; rfl

/-- The witness loop's data. -/
def mrOf (d : TD) : MrD :=
  ⟨d.q, d.mb, d.N, checkWitnesses d.N d.K (d.q.r.drop d.u), 0, d.u, d.K⟩

theorem testCore_ct (R : RoundImpl) :
    RelCT isa (Two TC) (.seq montPrep (millerRabin R.name R.code)) (Two ME) :=
  RelCT.seq (two_post (two_taintR _ pins_TC (by taint_decide_rel)) (Ψ := fun d => MI0 (mrOf d)) fun _ _ ⟨sv, toc, h⟩ =>
      WP.mono (montPrep_mst h.st h.ph h.mb1 h.mb2 h.n h.odd h.n3) fun _ ⟨M, _, h152⟩ =>
        ⟨⟨sv, toc, M, h152.trans h.used⟩, h.ul, rfl, rfl, h.bl⟩)
    (two_map mrOf (fun _ _ h => h) (millerRabin_ct R))

/-- A test's public data: the candidate and the tape's offset. -/
structure TQD where
  q : PP
  c : Nat
  u : Nat

/-- Before q's test. -/
def TQ (d : TQD) (s : State) : Prop :=
  ∃ sv toc, St (d.q.with sv toc) s ∧ d.c = Spec.Ffdh.candidateOf d.q.bits (Spec.Rsa.os2ip (d.q.r.take d.q.L)) ∧
    wv s.mem d.q.B (slot (wOf d.q.bits) 0) (wOf d.q.bits) = (d.c - 1) / 2 ∧ ((d.c - 1) / 2) % 2 = 1 ∧
    word s.mem d.q.B 152 = BitVec.ofNat 64 d.u ∧ d.u ≤ d.q.r.length

/-- q's test leaks the same from the same candidate and tape. -/
theorem testQ_ct (R : RoundImpl) : RelCT isa (Two TQ) (test true (.block []) R.name R.code) (Two ME) := by
  unfold test
  simp only [↓reduceIte]
  refine RelCT.assoc (RelCT.seq (two_post ?_
    (Ψ := fun d => TC ⟨d.q, d.q.bits - 1, (d.c - 1) / 2, d.u, Spec.Ffdh.primeChecks (d.q.bits - 1)⟩)
    fun _ _ ⟨sv, toc, h, hc, hq, hqo, hu, hul⟩ => WP.mono (qPrep_ok h hc hq hqo hu hul) fun _ ht => ⟨sv, toc, ht⟩)
    (RelCT.seq (two_post (two_map _ (fun _ _ h => h) (two_taint _ pins_TC (by taint_decide)))
      (Ψ := fun d => TC ⟨d.q, d.q.bits - 1, (d.c - 1) / 2, d.u, Spec.Ffdh.primeChecks (d.q.bits - 1)⟩)
      fun _ _ h => WP.block_nil h)
    (two_map _ (fun _ _ h => h) (testCore_ct R))))
  exact two_map TQD.q (fun _ _ ⟨sv, toc, h, _⟩ => ⟨sv, toc, h⟩)
    (RelCT.seq (phasePA_ct true) (two_taint _ (pins_PA true) (by taint_decide)))

/-- Before p's test. -/
def TP (d : TQD) (s : State) : Prop :=
  ∃ sv toc, St (d.q.with sv toc) s ∧ d.c = Spec.Ffdh.candidateOf d.q.bits (Spec.Rsa.os2ip (d.q.r.take d.q.L)) ∧
    word s.mem d.q.B 152 = BitVec.ofNat 64 d.u ∧ d.u ≤ d.q.r.length ∧ d.q.L ≤ d.q.r.length

/-- p's test, with `adjust` setting its count of witnesses to `Kf` of the
default, leaks the same from the same candidate and tape. -/
theorem testP_ct (R : RoundImpl) {adjust : Prog isa} (Kf : Nat → Nat)
    (hadj : ∀ {p : PP} {c u : Nat} {t : State}, TCPre p p.bits c u (Spec.Ffdh.primeChecks p.bits) t →
      WP isa adjust t (TCPre p p.bits c u (Kf (Spec.Ffdh.primeChecks p.bits))))
    (hct : RelCT isa (Two TC) adjust fun _ _ => True) :
    RelCT isa (Two TP) (test false adjust R.name R.code) (Two ME) := by
  unfold test
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine RelCT.assoc (RelCT.seq (two_post ?_
    (Ψ := fun d => TC ⟨d.q, d.q.bits, d.c, d.u, Spec.Ffdh.primeChecks d.q.bits⟩)
    fun _ _ ⟨sv, toc, h, hc, hu, hul, hL⟩ => WP.mono (pPrep_ok h hc hu hul hL) fun _ ht => ⟨sv, toc, ht⟩)
    (RelCT.seq (two_post (two_map _ (fun _ _ h => h) hct)
      (Ψ := fun d => TC ⟨d.q, d.q.bits, d.c, d.u, Kf (Spec.Ffdh.primeChecks d.q.bits)⟩)
      fun _ _ ⟨sv, toc, h⟩ => WP.mono (hadj h) fun _ ht => ⟨sv, toc, ht⟩)
    (two_map _ (fun _ _ h => h) (testCore_ct R))))
  exact two_map TQD.q (fun _ _ ⟨sv, toc, h, _⟩ => ⟨sv, toc, h⟩) (RelCT.seq (phasePA_ct false) shapeP_ct)

/-- p's test of its first witness. -/
theorem testP1_ct (R : RoundImpl) : RelCT isa (Two TP) (test false firstCheck R.name R.code) (Two ME) :=
  testP_ct R (fun _ => 1) (fun h => firstCheck_ok h) (two_taint _ pins_TC (by taint_decide))

/-- p's test of its other witnesses. -/
theorem testPR_ct (R : RoundImpl) : RelCT isa (Two TP) (test false restChecks R.name R.code) (Two ME) :=
  testP_ct R (· - 1) (fun h => restChecks_ok h (by unfold Spec.Ffdh.primeChecks; split <;> decide))
    (two_taint _ pins_TC (by taint_decide))

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on PPC64LE: the results in constant time

`finish` stores through `used`'s address, pinned once loaded from the
header; the results branch on a test's status, which its witnesses decide
(`statOf`); `writeP` copies p through `out`'s address and length, pinned
once loaded.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

/-- Before `finish`: the working space, and `used`'s address in its header. -/
def FS (q : PP) (s : State) : Prop :=
  ∃ Z, Scr s q.B Z ∧ 40 ≤ Z ∧ s.gpr .r31 = q.B ∧ s.mem.readW (q.B + BitVec.ofNat 64 32) 64 = q.up

theorem pins_FS : Pins FS [.r31] := by
  rintro q s₁ s₂ ⟨_, _, _, h₁, -⟩ ⟨_, _, _, h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁, h₂]

/-- With `used`'s address loaded. -/
def F4 (q : PP) (s : State) : Prop := s.gpr .r31 = q.B ∧ s.gpr .r4 = q.up

theorem pins_F4 : Pins F4 [.r4, .r31] := by
  rintro q s₁ s₂ ⟨a31, a4⟩ ⟨b31, b4⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a4, b4]
  · rw [a31, b31]

theorem St.fs {p : PP} {s : State} (h : St p s) : FS p s := by
  have := h.dims.n
  exact ⟨p.Z, h.scr, by simp only [PP.Z]; omega_using [this], h.r31, h.args.usedP'⟩

theorem finish_ct {r : Nat} (hr : r = 0 ∨ r = 1 ∨ r = 2) : RelCT isa (Two FS) (.block (finish r)) fun _ _ => True := by
  have hd : RelCT isa (Two FS) (.block [ldh .r4 hUsedP]) (Two F4) :=
    two_post (two_taint _ pins_FS (by taint_decide)) fun q s ⟨Z, hs, hZ, h31, hu⟩ =>
      WP.mono (WP.keep [.r4] (Q := fun t => t.gpr .r4 = q.up) (by
          simp only [ldh, hUsedP]; prun [h31, hs.ld (d := 32) (n := 8) (by omega_using [hZ]), hu]) (by decide))
        fun t ⟨t4, k⟩ => ⟨(k.gpr _ (by decide)).trans h31, t4⟩
  unfold finish
  rw [List.append_assoc]
  obtain rfl | rfl | rfl := hr
  all_goals exact RelCT.block_append (RelCT.seq hd (two_taint _ pins_F4 (by taint_decide)))

/-- A test's status: 0 without enough octets, 1 if it passed, 2 if not. -/
def statOf : Option (Bool × List Byte) → Nat
  | none => 0
  | some (b, _) => if b then 1 else 2

theorem statOf_le (r : Option (Bool × List Byte)) : statOf r ≤ 2 := by
  rcases r with _ | ⟨_ | _, _⟩ <;> simp [statOf]

theorem MrEnd.stat {C : Nat} {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)} {s : State}
    (h : MrEnd p mb N C res s) : word s.mem p.B 160 = BitVec.ofNat 64 (statOf res) := by
  obtain ⟨_, hn, hs⟩ := h
  rcases res with _ | ⟨b, rest⟩
  · exact hn rfl
  · exact (hs b rest rfl).1

theorem MSt.fs {C : Nat} {p : PP} {mb N : Nat} {s : State} (h : MSt p mb N C s) : FS p s := h.st.fs

theorem pins_ME : Pins ME [.r31] := by
  rintro a s₁ s₂ ⟨_, _, h₁, -⟩ ⟨_, _, h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.st.r31, h₂.st.r31]; rfl

/-- With a test's status in `r3`. -/
def SL (a : MrD) (t : State) : Prop :=
  (∃ sv toc, MSt (a.q.with sv toc) a.mb a.N a.K t) ∧ t.gpr .r3 = BitVec.ofNat 64 (statOf a.res)

theorem statLoad_ct : RelCT isa (Two ME) (.block [ldh .r3 hStat]) (Two SL) :=
  two_post (two_taint _ pins_ME (by taint_decide)) fun _ _ ⟨sv, toc, hE⟩ =>
    WP.mono (statLoad_ok hE.1) fun _ ⟨Mt, t3, _⟩ => ⟨⟨sv, toc, Mt⟩, t3.trans hE.stat⟩

theorem finSL_ct {r : Nat} (hr : r = 0 ∨ r = 1 ∨ r = 2) {Φ : MrD → State → Prop}
    (h : ∀ a s, Φ a s → ∃ sv toc, MSt (a.q.with sv toc) a.mb a.N a.K s) :
    RelCT isa (Two Φ) (.block (finish r)) fun _ _ => True :=
  two_map MrD.q (fun a s hs => let ⟨_, _, M⟩ := h a s hs; M.fs) (finish_ct hr)


/-- After a failed test of q. -/
theorem qResult_ct : RelCT isa (Two ME) qResult fun _ _ => True := by
  unfold qResult
  refine RelCT.seq statLoad_ct (two_ite' (fun a => decide (statOf a.res = 0)) (fun a s h => ?_)
    (finSL_ct (.inl rfl) fun _ _ h => h.1.1) (finSL_ct (.inr (.inr rfl)) fun _ _ h => h.1.1))
  exact eval_zero_ofNat s .r3 (by have := statOf_le a.res; omega_using [this]) h.2

/-- With a test's status less one in `r3`. -/
def SL1 (a : MrD) (t : State) : Prop :=
  (∃ sv toc, MSt (a.q.with sv toc) a.mb a.N a.K t) ∧ t.gpr .r3 = BitVec.ofNat 64 (statOf a.res) - BitVec.ofNat 64 1

/-- In a modulus's working space. -/
def MS (a : MrD) (t : State) : Prop := ∃ sv toc, MSt (a.q.with sv toc) a.mb a.N a.K t

theorem pins_MS {Φ : MrD → State → Prop} (h : ∀ a s, Φ a s → MS a s) : Pins Φ [.r31] := by
  intro a s₁ s₂ h₁ h₂ r hr
  obtain ⟨_, _, M₁⟩ := h a s₁ h₁
  obtain ⟨_, _, M₂⟩ := h a s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [M₁.st.r31, M₂.st.r31]; rfl

theorem sub1_ct {Φ : MrD → State → Prop} (h : ∀ a s, Φ a s → SL a s) :
    RelCT isa (Two Φ) (.block [.subi .r3 .r3 1]) (Two SL1) :=
  two_post (two_taint _ (pins_MS fun a s hs => (h a s hs).1) (by taint_decide)) fun a s hs => by
    obtain ⟨⟨sv, toc, M⟩, h3⟩ := h a s hs
    exact WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 (statOf a.res) - BitVec.ofNat 64 1 ∧
        t.mem = s.mem) (by prun [h3]) (by decide)) fun t ⟨⟨t3, tm⟩, k⟩ =>
      ⟨⟨sv, toc, M.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k (by decide) (k.gpr _ (by decide))
        (k.gpr _ (by decide)) (k.gpr _ (by decide))⟩, t3⟩

/-- With `out`, `out_len` and p's last octet's address loaded. -/
def W4 (a : MrD) (t : State) : Prop :=
  t.gpr .r4 = a.q.op ∧ t.gpr .r5 = BitVec.ofNat 64 a.q.L ∧ t.gpr .r6 = off a.q.B (256 + (a.q.L - 1))

theorem pins_W4 : Pins W4 [.r4, .r5, .r6] := by
  rintro a s₁ s₂ ⟨a4, a5, a6⟩ ⟨b4, b5, b6⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a4, b4]
  · rw [a5, b5]
  · rw [a6, b6]

theorem writeP_ct {Φ : MrD → State → Prop} (h : ∀ a s, Φ a s → MS a s) :
    RelCT isa (Two Φ) writeP (Two fun (a : MrD) => FS a.q) := by
  refine two_post ?_ fun a s hs => ?_
  · unfold writeP
    refine RelCT.seq (two_post (two_taint _ (pins_MS h) (by taint_decide)) (Ψ := W4) fun a s hs => ?_)
      (two_taint _ pins_W4 (by taint_decide))
    obtain ⟨sv, toc, M⟩ := h a s hs
    have hdn := M.st.dims.n
    have hb1 := M.st.dims.b1
    have hLe : (a.q.with sv toc).L = ((a.q.with sv toc).bits + 7) / 8 := rfl
    have hZe : (a.q.with sv toc).Z = 8 * (a.q.with sv toc).n := rfl
    exact WP.mono (writeHead_ok M.st.scr M.st.r31 (M.ph.r10.trans (by rw [slot_zero])) M.st.args.out'
      M.st.args.len' (by omega_using [hb1, hLe]) (by omega_using [hdn, hZe])) fun t ⟨⟨t6, t4, t5, _⟩, _⟩ => ⟨t4, t5, t6⟩
  · obtain ⟨sv, toc, M⟩ := h a s hs
    have h := M.st
    have hdn := h.dims.n
    have hb1 := h.dims.b1
    have hnw := h.scr.nowrap
    have hLe : (a.q.with sv toc).L = ((a.q.with sv toc).bits + 7) / 8 := rfl
    have hZe : (a.q.with sv toc).Z = 8 * (a.q.with sv toc).n := rfl
    refine WP.mono (writeP_ok h.scr h.bufs.scrO h.r31 (M.ph.r10.trans (by rw [slot_zero])) h.args.out'
      h.args.len' (by omega_using [hb1, hLe]) (by omega_using [hdn, hZe]) h.bufs.sepO) fun t₁ ⟨⟨_, tout⟩, k₁⟩ => ?_
    have hws₁ : ∀ x, ofs (a.q.with sv toc).B x < (a.q.with sv toc).Z → t₁.mem x = s.mem x := fun x hx => tout x (Or.inr (by
      by_contra hc'
      have := h.bufs.sepO x (by omega_using [hc'])
      omega_using [hx, this]))
    have E₁ := h.toE.frame hws₁ k₁ (by decide)
    exact ⟨_, E₁.scr, by omega_using [hdn, hZe], E₁.r31, (word_of_ws hws₁ (d := 32) (by omega_using [hdn, hZe]) hnw).trans h.args.usedP'⟩

/-- After p's test. -/
theorem pResult_ct : RelCT isa (Two ME) pResult fun _ _ => True := by
  unfold pResult
  refine RelCT.seq statLoad_ct (two_ite' (fun a => decide (statOf a.res = 0))
    (fun a s h => eval_zero_ofNat s .r3 (by have := statOf_le a.res; omega_using [this]) h.2)
    (finSL_ct (.inl rfl) fun _ _ h => h.1.1) ?_)
  refine RelCT.seq (sub1_ct fun _ _ h => h.1) (two_ite' (fun a => decide (statOf a.res = 1)) (fun a s h => ?_)
    (RelCT.seq (writeP_ct fun _ _ h => h.1.1) (two_map MrD.q (fun _ _ h => h) (finish_ct (.inr (.inl rfl)))))
    (finSL_ct (.inr (.inr rfl)) fun _ _ h => h.1.1))
  rw [eval_zero, h.2]
  exact congrArg some (stat_one (by have := statOf_le a.res; omega_using [this]))

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on PPC64LE: the tests in constant time

p's first witness, then a branch on its status, which its witnesses
decide; q, from p, and its test, from the offset in the tape where p's
left off (`d2`), then a branch on its status; p's other witnesses (`d3`),
then the result.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

theorem pins_r31 {α : Type} {Φ : α → State → Prop} (B : α → Addr) (h : ∀ a s, Φ a s → s.gpr .r31 = B a) :
    Pins Φ [.r31] := by
  intro a s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h a _ h₁, h a _ h₂]

theorem MrEnd.of_mem {C : Nat} {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)} {s t : State}
    (h : MrEnd p mb N C res s) (M : MSt p mb N C t) (hm : t.mem = s.mem) : MrEnd p mb N C res t :=
  ⟨M, fun h' => by rw [hm]; exact h.2.1 h', fun b r h' => by rw [hm]; exact h.2.2 b r h'⟩

/-- The candidate's facts the tests carry. -/
def FX (d : TQD) : Prop :=
  d.c = Spec.Ffdh.candidateOf d.q.bits (Spec.Rsa.os2ip (d.q.r.take d.q.L)) ∧ d.q.L ≤ d.q.r.length ∧
    ((d.c - 1) / 2) % 2 = 1

/-- Before the tests. -/
def TS (d : TQD) (s : State) : Prop := TP d s ∧ ((d.c - 1) / 2) % 2 = 1

/-- After a test whose data are `E d`. -/
def TE (E : TQD → MrD) (d : TQD) (t : State) : Prop := ME (E d) t ∧ FX d

/-- The rest of the tape after a test's witnesses. -/
def restOf : Option (Bool × List Byte) → List Byte
  | none => []
  | some (_, r) => r

/-- The tape's offset after a test's witnesses. -/
def uAfter (res : Option (Bool × List Byte)) (q : PP) : Nat := q.r.length - (restOf res).length

theorem ME.passed {a : MrD} {t : State} (h : ME a t) (h1 : statOf a.res = 1) :
    ∃ sv toc, MSt (a.q.with sv toc) a.mb a.N a.K t ∧
      word t.mem a.q.B 152 = BitVec.ofNat 64 (uAfter a.res a.q) ∧ uAfter a.res a.q ≤ a.q.r.length := by
  obtain ⟨sv, toc, M, -, hsome⟩ := h
  revert h1 hsome
  unfold uAfter
  generalize a.res = r
  intro h1 hsome
  rcases r with _ | ⟨_ | _, rest⟩
  · simp [statOf] at h1
  · simp [statOf] at h1
  · obtain ⟨-, u, hul, hr, hU⟩ := hsome true rest rfl
    have hul' : u ≤ a.q.r.length := hul
    have eu : a.q.r.length - (restOf (some (true, rest))).length = u := by
      subst hr; show a.q.r.length - (a.q.r.drop u).length = u; rw [List.length_drop]; omega_using [hul']
    exact ⟨sv, toc, M, by rw [eu]; exact hU, by rw [eu]; exact hul'⟩

theorem pins_TE (E : TQD → MrD) {Φ : TQD → State → Prop} (h : ∀ d s, Φ d s → TE E d s) :
    Pins Φ [.r10, .r11, .r29, .r31] := by
  intro d s₁ s₂ h₁ h₂ r hr
  obtain ⟨⟨_, _, M₁, -⟩, -⟩ := h d s₁ h₁
  obtain ⟨⟨_, _, M₂, -⟩, -⟩ := h d s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [M₁.ph.r10, M₂.ph.r10]; rfl
  · rw [M₁.ph.r11, M₂.ph.r11]
  · rw [M₁.ph.r29, M₂.ph.r29]
  · rw [M₁.st.r31, M₂.st.r31]; rfl

/-- After a test whose data are `E d`: `qResult` unless it passed, else
`cont`. -/
theorem stage_ct (E : TQD → MrD) {cont : Prog isa}
    (hc : RelCT isa (Two fun d t => TE E d t ∧ statOf (E d).res = 1) cont fun _ _ => True) :
    RelCT isa (Two (TE E)) (.seq (.block [ldh .r3 hStat, .subi .r3 .r3 1]) (.ite (.zero .d .r3) cont qResult))
      fun _ _ => True := by
  have hs : RelCT isa (Two (TE E)) (.block [ldh .r3 hStat, .subi .r3 .r3 1])
      (Two fun d t => isa.eval (.zero .d .r3) t = some (decide (statOf (E d).res = 1)) ∧ TE E d t) :=
    two_post (two_taint _ (pins_TE E fun _ _ h => h) (by taint_decide)) fun d _ ⟨⟨sv, toc, hE⟩, hx⟩ =>
      WP.mono (stat1_ok hE.1 (v := statOf (E d).res) (by have := statOf_le (E d).res; omega_using [this]) hE.stat)
        fun _ ⟨he, M, hm⟩ => ⟨he, ⟨sv, toc, hE.of_mem M hm⟩, hx⟩
  exact RelCT.seq hs (two_ite' (fun d => decide (statOf (E d).res = 1)) (fun _ _ h => h.1)
    (two_mono (fun _ _ h => ⟨h.1.2, of_decide_eq_true h.2⟩) hc) (two_map E (fun _ _ h => h.1.2.1) qResult_ct))

/-- p's first witness. -/
def E1 (d : TQD) : MrD := mrOf ⟨d.q, d.q.bits, d.c, d.u, 1⟩

/-- q's test's data. -/
def d2 (d : TQD) : TQD := ⟨d.q, d.c, uAfter (E1 d).res d.q⟩

/-- q's witnesses. -/
def E2 (d : TQD) : MrD := mrOf ⟨d.q, d.q.bits - 1, (d.c - 1) / 2, (d2 d).u, Spec.Ffdh.primeChecks (d.q.bits - 1)⟩

/-- The test of p's other witnesses' data. -/
def d3 (d : TQD) : TQD := ⟨d.q, d.c, uAfter (E2 d).res d.q⟩

/-- p's other witnesses. -/
def E3 (d : TQD) : MrD := mrOf ⟨d.q, d.q.bits, d.c, (d3 d).u, Spec.Ffdh.primeChecks d.q.bits - 1⟩

/-- p's other witnesses and the result leak the same. -/
theorem testRest_ct (R : RoundImpl) :
    RelCT isa (Two fun d t => TE E2 d t ∧ statOf (E2 d).res = 1) (testRest R.name R.code) fun _ _ => True := by
  unfold testRest
  have hp : ∀ d t, TE E2 d t ∧ statOf (E2 d).res = 1 → TP (d3 d) t := fun d t ⟨⟨hE, hc, hL, _⟩, h1⟩ => by
    obtain ⟨sv, toc, M, hU, hu⟩ := hE.passed h1
    exact ⟨sv, toc, M.st, hc, hU, hu, hL⟩
  refine RelCT.seq (two_post ((two_map d3 hp (testPR_ct R)).mono (fun _ _ h => h) fun _ _ _ => trivial)
    (Ψ := fun d => ME (E3 d)) fun d _ h => ?_) (two_map E3 (fun _ _ h => h) pResult_ct)
  obtain ⟨sv, toc, st, hc, hU, hu, hL⟩ := hp d _ h
  exact WP.mono (testPR_ok R st hc hU hu hL) fun _ ht => ⟨sv, toc, ht⟩

/-- q, from p, its test and the rest leak the same. -/
theorem testQ_cts (R : RoundImpl) :
    RelCT isa (Two fun d t => TE E1 d t ∧ statOf (E1 d).res = 1) (testQ R.name R.code) fun _ _ => True := by
  unfold testQ
  have hh : RelCT isa (Two fun d t => TE E1 d t ∧ statOf (E1 d).res = 1) halveQ
      (Two fun d t => TQ (d2 d) t ∧ FX d) :=
    two_post (two_taint _ (pins_TE E1 fun _ _ h => h.1) (by taint_decide)) fun d _ ⟨⟨hE, hx⟩, h1⟩ => by
      obtain ⟨sv, toc, M, hU, hu⟩ := hE.passed h1
      exact WP.mono (halveQ_from M hx.1 hU) fun _ ⟨st, hq, hU'⟩ => ⟨⟨sv, toc, st, hx.1, hq, hx.2.2, hU', hu⟩, hx⟩
  have hq : RelCT isa (Two fun d t => TQ (d2 d) t ∧ FX d) (test true (.block []) R.name R.code) (Two (TE E2)) :=
    two_post ((two_map d2 (fun _ _ h => h.1) (testQ_ct R)).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun _ _ ⟨⟨sv, toc, h, hc, hq, hqo, hu, hul⟩, hx⟩ =>
        WP.mono (testQ_ok R h hc hq hqo hu hul) fun _ ht => ⟨⟨sv, toc, ht⟩, hx⟩
  exact RelCT.seq hh (RelCT.seq hq (stage_ct E2 (testRest_ct R)))

/-- The tests leak the same from the same candidate and tape. -/
theorem tests_ct (R : RoundImpl) : RelCT isa (Two TS) (tests R.name R.code) fun _ _ => True := by
  unfold tests
  have h1 : RelCT isa (Two TS) (test false firstCheck R.name R.code) (Two (TE E1)) :=
    two_post ((two_mono (fun _ _ h => h.1) (testP1_ct R)).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun _ _ ⟨⟨sv, toc, h, hc, hu, hul, hL⟩, hqo⟩ =>
        WP.mono (testP1_ok R h hc hu hul hL) fun _ ht => ⟨⟨sv, toc, ht⟩, hc, hL, hqo⟩
  exact RelCT.seq h1 (stage_ct E1 (testQ_cts R))

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on PPC64LE: `main` in constant time

The public data are the arguments and tape, and the table's address
(`taintSym`: the contract makes it public). p's congruence branches on the
generator, pinned once loaded; the shape checks branch on `hBad`, which the
candidate decides (`MB`), as do whether q's and p's whole checks run;
trial division (`trialSieve_ct`, `trialSieveN_ct`) loops while the
entry tested, a function of the candidate and of how many are left, does
not divide it; the tests are `tests_ct`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

/-- The candidate from the tape. -/
def candOf (q : PP) : Nat := Spec.Ffdh.candidateOf q.bits (Spec.Rsa.os2ip (q.r.take q.L))

/-- Code the taint analysis with the table's address public proves constant
time, from states a predicate relates. -/
theorem two_taint_sym {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    (hsym : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ →
      s₁.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s₂.syms VG.Impl.RsaKeyGen.TrialTable32.symbol)
    {hc : VG.Taint.Hint T}
    (h : (VG.Taint.check (taintSym [VG.Impl.RsaKeyGen.TrialTable32.symbol]) (ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taintSym [VG.Impl.RsaKeyGen.TrialTable32.symbol]) (ofRegs rs) (fun _ _ ⟨a, h₁, h₂, hsp⟩ =>
    ⟨⟨hsp, fun r hr => hpin a _ _ h₁ h₂ r (RegSet.mem_ofList.mp hr)⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsym a _ _ h₁ h₂⟩) h

/-- Before `main`: the arguments and tape, and the table's address. -/
def MnI (a : PP × Addr) (s : State) : Prop :=
  ∃ sv toc, St (a.1.with sv toc) s ∧ TabIn a.1.B a.1.Z a.2 s ∧ word s.mem a.1.B 152 = BitVec.ofNat 64 a.1.L ∧
    a.1.L ≤ a.1.r.length

/-- With p in array 0. -/
def MnA (a : PP × Addr) (t : State) : Prop :=
  (∃ sv toc, St (a.1.with sv toc) t ∧ TabIn a.1.B a.1.Z a.2 t ∧ Ph (a.1.with sv toc) a.1.bits
    (Spec.Ffdh.primeChecks a.1.bits) t ∧ word t.mem a.1.B 152 = BitVec.ofNat 64 a.1.L ∧
    wv t.mem a.1.B (slot (wOf a.1.bits) 0) (wOf a.1.bits) = candOf a.1) ∧ a.1.L ≤ a.1.r.length

/-- In p's working space, `hBad` zero iff `B q`. -/
def MnB (x : PP → Nat) (B : PP → Prop) (a : PP × Addr) (t : State) : Prop :=
  (∃ sv toc, MB (a.1.with sv toc) a.2 (x a.1) (B a.1) t) ∧ a.1.L ≤ a.1.r.length

theorem pins_MnB {x : PP → Nat} {B : PP → Prop} {Φ : PP × Addr → State → Prop}
    (h : ∀ a s, Φ a s → MnB x B a s) : Pins Φ [.r10, .r11, .r29, .r31] := by
  intro a s₁ s₂ h₁ h₂ r hr
  obtain ⟨⟨_, _, M₁⟩, _⟩ := h a s₁ h₁
  obtain ⟨⟨_, _, M₂⟩, _⟩ := h a s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [M₁.ph.r10, M₂.ph.r10]; rfl
  · rw [M₁.ph.r11, M₂.ph.r11]; rfl
  · rw [M₁.ph.r29, M₂.ph.r29]; rfl
  · rw [M₁.st.r31, M₂.st.r31]; rfl

theorem mainA_ct : RelCT isa (Two MnI) (.seq (phase false) shapeP) (Two MnA) :=
  two_post (two_map Prod.fst (fun _ _ ⟨sv, toc, h, _⟩ => ⟨sv, toc, h⟩) (RelCT.seq (phasePA_ct false) shapeP_ct))
    fun _ _ ⟨sv, toc, h, ht, hU, hL⟩ => WP.mono_syms (mainA_ok h hU hL) fun _ ⟨a, b, c, d, hr, f, rd⟩ sy =>
      ⟨⟨sv, toc, a, ht.step sy f hr rd, b, c, d⟩, hL⟩

/-- After the congruence's first block. -/
def RH (a : PP × Addr) (t : State) : Prop :=
  (t.gpr .r3 = BitVec.ofNat 64 a.1.g - BitVec.ofNat 64 2 ∧ (a.1.g = 2 ∨ a.1.g = 5)) ∧
    t.gpr .r10 = off a.1.B (slot (wOf a.1.bits) 0) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * wOf a.1.bits) ∧
    t.gpr .r31 = a.1.B

theorem pins_RH {Φ : PP × Addr → State → Prop} (h : ∀ a s, Φ a s → RH a s) : Pins Φ [.r10, .r11, .r31] := by
  intro a s₁ s₂ h₁ h₂ r hr
  obtain ⟨_, a10, a11, a31⟩ := h a s₁ h₁
  obtain ⟨_, b10, b11, b31⟩ := h a s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a31, b31]

theorem pins_MnA : Pins MnA [.r31] := by
  rintro a s₁ s₂ ⟨⟨_, _, h₁, _⟩, _⟩ ⟨⟨_, _, h₂, _⟩, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.r31, h₂.r31]; rfl

theorem residue_ct :
    RelCT isa (Two MnA) residue (Two (MnB candOf fun q => goodRes q.g (candOf q))) := by
  refine two_post ?_ fun _ _ ⟨⟨sv, toc, h, ht, hp, hU, hn⟩, hL⟩ =>
    WP.mono (residue_mb h hp ht hU hn) fun _ M => ⟨⟨sv, toc, M⟩, hL⟩
  unfold residue
  refine RelCT.seq (two_post (two_taint _ pins_MnA (by taint_decide)) (Ψ := RH)
    fun a s ⟨⟨sv, toc, h, _, hp, _⟩, _⟩ => ?_) (two_ite' (fun a => decide (a.1.g = 2)) (fun a s h => ?_)
      (two_taint _ (pins_RH fun _ _ h => h.1) (by taint_decide))
      (two_taint _ (pins_RH fun _ _ h => h.1) (by taint_decide)))
  · refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 a.1.g - BitVec.ofNat 64 2) ?_
      (by decide)) fun t ⟨t3, k⟩ => ⟨⟨t3, h.dims.g⟩, (k.gpr _ (by decide)).trans hp.r10,
        (k.gpr _ (by decide)).trans hp.r11, (k.gpr _ (by decide)).trans h.r31⟩
    simp only [ldh, hGen]
    prun [h.r31, h.ld (d := 128) (by decide), h.args.gen', BitVec.add_zero]
    rfl
  · obtain ⟨⟨h3, hg⟩, _⟩ := h
    rw [eval_zero, h3]
    rcases hg with hg | hg <;> rw [hg] <;> decide

theorem badLoad_ct {x : PP → Nat} {B : PP → Prop} [∀ q, Decidable (B q)] :
    RelCT isa (Two (MnB x B)) (.block [ldh .r5 hBad])
      (Two fun a t => MnB x B a t ∧ isa.eval (.zero .d .r5) t = some (decide (B a.1))) :=
  two_post (two_taint _ (pins_MnB fun _ _ h => h) (by taint_decide)) fun _ _ ⟨⟨sv, toc, M⟩, hL⟩ =>
    WP.mono M.badLoad fun _ ⟨M', t5⟩ => ⟨⟨⟨sv, toc, M'⟩, hL⟩,
      (by rw [eval_zero, t5]; exact congrArg some (beq_zero_of_iff M.bad))⟩

theorem finMnB_ct {x : PP → Nat} {B : PP → Prop} {Φ : PP × Addr → State → Prop}
    (h : ∀ a s, Φ a s → MnB x B a s) : RelCT isa (Two Φ) (.block (finish 2)) fun _ _ => True :=
  two_map Prod.fst (fun a s hs => let ⟨⟨_, _, M⟩, _⟩ := h a s hs; M.st.fs) (finish_ct (.inr (.inr rfl)))

theorem halve_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnB x B)) halveQ (Two (MnB (fun q => x q / 2) fun q => B q ∧ x q / 2 % 2 = 1)) :=
  two_post (two_taint _ (pins_MnB fun _ _ h => h) (by taint_decide)) fun _ _ ⟨⟨sv, toc, M⟩, hL⟩ =>
    WP.mono M.halve fun _ M' => ⟨⟨sv, toc, M'⟩, hL⟩

/-! ## Trial division by products of four entries -/

/-- With the table's address and the count `N q` in `r23` and `r24`. -/
def MnPT (x : PP → Nat) (B : PP → Prop) (N : PP → Nat) (a : PP × Addr) (v : State) : Prop :=
  ∃ u, MnB x B a u ∧ (v.gpr .r23 = a.2 ∧ v.gpr .r24 = BitVec.ofNat 64 (N a.1) ∧ v.mem = u.mem) ∧
    (∀ r, r ∉ [Reg.r3, Reg.r4, Reg.r23, Reg.r24] → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧ v.wr = u.wr ∧
    v.sp = u.sp ∧ v.syms = u.syms

/-- In the loop, `d.2` groups left. -/
def MnPL (x : PP → Nat) (B : PP → Prop) (N : PP → Nat) (d : (PP × Addr) × Nat) (w : State) : Prop :=
  ∃ v, MnPT x B N d.1 v ∧ LInv v d.1.1.B d.1.2 (x d.1.1) (N d.1.1) d.2 w

/-- After the loop. -/
def MnPE (x : PP → Nat) (B : PP → Prop) (N : PP → Nat) (d : (PP × Addr) × Nat) (w : State) : Prop :=
  ∃ v, MnPT x B N d.1 v ∧ Keep groupRegs v w

theorem MnPT.base {x : PP → Nat} {B : PP → Prop} {N : PP → Nat} {a : PP × Addr} {v : State}
    (h : MnPT x B N a v) :
    v.gpr .r10 = off a.1.B (slot (wOf a.1.bits) 0) ∧ v.gpr .r11 = BitVec.ofNat 64 (2 * wOf a.1.bits) ∧
      v.gpr .r31 = a.1.B := by
  obtain ⟨u, ⟨⟨_, _, M⟩, _⟩, -, vg, -⟩ := h
  exact ⟨(vg _ (by decide)).trans M.ph.r10, (vg _ (by decide)).trans M.ph.r11, (vg _ (by decide)).trans M.st.r31⟩

theorem pins_MnPL {x : PP → Nat} {B : PP → Prop} {N : PP → Nat} :
    Pins (MnPL x B N) [.r10, .r11, .r23, .r31] := by
  rintro d s₁ s₂ ⟨v₁, hv₁, k₁, hm₁, hk₁, ⟨a23, -⟩, kv₁⟩ ⟨v₂, hv₂, k₂, hm₂, hk₂, ⟨b23, -⟩, kv₂⟩ r hr
  obtain ⟨a10, a11, a31⟩ := hv₁.base
  obtain ⟨b10, b11, b31⟩ := hv₂.base
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [kv₁.gpr _ (by decide), kv₂.gpr _ (by decide), a10, b10]
  · rw [kv₁.gpr _ (by decide), kv₂.gpr _ (by decide), a11, b11]
  · rw [a23, b23, show k₁ = k₂ by omega]
  · rw [kv₁.gpr _ (by decide), kv₂.gpr _ (by decide), a31, b31]

theorem pins_MnPE {x : PP → Nat} {B : PP → Prop} {N : PP → Nat} : Pins (MnPE x B N) [.r31] := by
  rintro d s₁ s₂ ⟨v₁, hv₁, kv₁⟩ ⟨v₂, hv₂, kv₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [kv₁.gpr _ (by decide), kv₂.gpr _ (by decide), hv₁.base.2.2, hv₂.base.2.2]

theorem MnPT.init {x : PP → Nat} {B : PP → Prop} {N : PP → Nat} {a : PP × Addr} {v : State}
    (hN : 4 ≤ N a.1) (h : MnPT x B N a v) : MnPL x B N (a, N a.1 / 4) v := by
  obtain ⟨u, -, ⟨v23, v24, -⟩, -⟩ := id h
  refine ⟨v, h, 0, by dsimp only; omega_using [], by dsimp only; omega_using [hN], ⟨?_, ?_, ?_, Frm.refl _ _ _⟩, Keep.refl _ _⟩
  · rw [v23]; exact (BitVec.add_zero _).symm
  · rw [v24]; rfl
  · simp [VG.Proof.RsaKeyGen.trialPrefix]

/-- The go-on condition of the loop, `d.2` groups left. -/
def prodGo (x : PP → Nat) (N : PP → Nat) (d : (PP × Addr) × Nat) : Bool :=
  lgo (x d.1.1) (N d.1.1) (N d.1.1 / 4 - d.2)

theorem MnPL.step {x : PP → Nat} {B : PP → Prop} {N : PP → Nat}
    (hN : ∀ q, N q % 4 = 0 ∧ 4 ≤ N q ∧ N q ≤ 1024) {d : (PP × Addr) × Nat} {w : State} (h : MnPL x B N d w) :
    WP isa prodGroup w fun t =>
      isa.eval (.nonzero .d .r24) t = some (prodGo x N d) ∧ (prodGo x N d = false → MnPE x B N d t) ∧
        (prodGo x N d = true → d.2 - 1 < d.2 ∧ MnPL x B N (d.1, d.2 - 1) t) := by
  obtain ⟨v, hv, hI⟩ := h
  obtain ⟨u, ⟨⟨sv, toc, M⟩, _⟩, ⟨_, _, vm⟩, vg, vrd, vwr, -⟩ := id hv
  have ha := M.largs vm vg vrd vwr (hN d.1.1).1 (hN d.1.1).2.1 (hN d.1.1).2.2
  refine WP.mono (lstep_ok ha hI) fun t ⟨e, f, g⟩ => ⟨e, fun hg => ⟨v, hv, (f hg).2⟩, fun hg => ?_⟩
  obtain ⟨hm, hI'⟩ := g hg
  exact ⟨by omega_using [hm], v, hv, hI'⟩

theorem prodLoop_ct {x : PP → Nat} {B : PP → Prop} {N : PP → Nat}
    (hN : ∀ q, N q % 4 = 0 ∧ 4 ≤ N q ∧ N q ≤ 1024) :
    RelCT isa (Two (MnPT x B N)) prodLoop (Two (MnPE x B N)) :=
  two_map (fun a => (a, N a.1 / 4)) (fun _ _ h => h.init (hN _).2.1)
    (two_loopD (Φ := MnPL x B N) (Ψ := MnPE x B N) Prod.snd (fun d => (d.1, d.2 - 1)) (prodGo x N)
      (two_taint _ pins_MnPL (by taint_decide)) fun _ _ h => h.step hN)

/-- Trial division by the first entries, by products, leaks the same from
the same candidate and table. -/
theorem prodSieveN_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnB x B)) (prodSieveN firstEntries)
      (Two (MnB x fun q => B q ∧ VG.Proof.RsaKeyGen.trialPrefix (x q) firstEntries = false)) := by
  refine two_post ?_ fun _ _ ⟨⟨sv, toc, M⟩, hL⟩ =>
    WP.mono (prodSieveN_ok M (by decide) (by decide) (by decide)) fun _ M' => ⟨⟨sv, toc, M'⟩, hL⟩
  unfold prodSieveN
  refine RelCT.seq (two_post (two_taint_sym _ (pins_MnB fun _ _ h => h)
      (fun _ _ _ ⟨⟨_, _, M₁⟩, _⟩ ⟨⟨_, _, M₂⟩, _⟩ => M₁.tab.sym.trans M₂.tab.sym.symm) (by unfold firstEntries; taint_decide))
    (Ψ := MnPT x B fun _ => firstEntries) fun _ u hu => ?_)
    (RelCT.seq (prodLoop_ct fun _ => by decide) (two_taint _ pins_MnPE (by taint_decide)))
  obtain ⟨⟨sv, toc, M⟩, hL⟩ := hu
  exact WP.mono (M.prodA firstEntries (by decide)) fun v hv =>
    ⟨u, ⟨⟨sv, toc, M⟩, hL⟩, hv.1, fun r hr => hv.2.1 r fun h' => hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')),
      hv.2.2⟩

/-- So does trial division by `trialN` entries, by products. -/
theorem prodSieve_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnB x B)) prodSieve
      (Two (MnB x fun q => B q ∧ VG.Proof.RsaKeyGen.trialPrefix (x q) (trialN q.bits) = false)) := by
  refine two_post ?_ fun _ _ ⟨⟨sv, toc, M⟩, hL⟩ => WP.mono (prodSieve_ok M) fun _ M' => ⟨⟨sv, toc, M'⟩, hL⟩
  unfold prodSieve
  refine RelCT.seq (two_post (two_taint_sym _ (pins_MnB fun _ _ h => h)
      (fun _ _ _ ⟨⟨_, _, M₁⟩, _⟩ ⟨⟨_, _, M₂⟩, _⟩ => M₁.tab.sym.trans M₂.tab.sym.symm) (by taint_decide))
    (Ψ := MnPT x B fun q => trialN q.bits) fun _ u hu => ?_)
    (RelCT.seq (prodLoop_ct fun _ => by unfold trialN; split <;> decide) (two_taint _ pins_MnPE (by taint_decide)))
  obtain ⟨⟨sv, toc, M⟩, hL⟩ := hu
  exact WP.mono M.prodC fun v hv => ⟨u, ⟨⟨sv, toc, M⟩, hL⟩, hv⟩

/-- p into array 0 again leaks the same. -/
theorem reshape_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnB x B)) shapeP (Two (MnB candOf B)) :=
  two_post (two_map (fun a => a.1) (fun _ _ ⟨⟨sv, toc, M⟩, _⟩ => ⟨sv, toc, _, M.st, M.ph⟩) shapeP_ct)
    fun _ _ ⟨⟨sv, toc, M⟩, hL⟩ => WP.mono (M.reshape hL) fun _ M' => ⟨⟨sv, toc, M'⟩, hL⟩

/-! ## `main` -/

/-- The congruence and p's trial division by the first entries. -/
def pOk (q : PP) : Prop :=
  goodRes q.g (candOf q) ∧ VG.Proof.RsaKeyGen.trialPrefix (candOf q) firstEntries = false

instance (q : PP) : Decidable (pOk q) := by unfold pOk; infer_instance

/-- Then q's parity and trial division. -/
def qOk (q : PP) : Prop :=
  (pOk q ∧ candOf q / 2 % 2 = 1) ∧ VG.Proof.RsaKeyGen.trialPrefix (candOf q / 2) (trialN q.bits) = false

instance (q : PP) : Decidable (qOk q) := by unfold qOk; infer_instance

/-- The shape checks' conjunction, after p's whole trial division. -/
def allOk (q : PP) : Prop :=
  qOk q ∧ VG.Proof.RsaKeyGen.trialPrefix (candOf q) (trialN q.bits) = false

instance (q : PP) : Decidable (allOk q) := by unfold allOk; infer_instance

theorem ts_of {a : PP × Addr} {s : State} (h : MnB candOf allOk a s) (ha : allOk a.1) :
    TS ⟨a.1, candOf a.1, a.1.L⟩ s := by
  obtain ⟨⟨sv, toc, M⟩, hL⟩ := h
  have hb1 : 512 ≤ a.1.bits := M.st.dims.b1
  obtain ⟨ho, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := a.1.bits) (by omega_using [hb1])
    (Spec.Rsa.os2ip (a.1.r.take a.1.L))
  have hq : (candOf a.1 - 1) / 2 = candOf a.1 / 2 := by unfold candOf; omega_using [ho]
  exact ⟨⟨sv, toc, M.st, rfl, M.u, hL, hL⟩, by rw [hq]; exact ha.1.1.2⟩

/-- `mainP` leaks the same from the same arguments, tape and table. -/
theorem mainP_ct (R : RoundImpl) :
    RelCT isa (Two (MnB (fun q => candOf q / 2) qOk)) (mainP R.name R.code) fun _ _ => True := by
  unfold mainP
  refine RelCT.seq reshape_ct (RelCT.seq prodSieve_ct (RelCT.seq (badLoad_ct (B := allOk))
    (two_ite' (fun a => decide (allOk a.1)) (fun _ _ h => h.2) ?_ (finMnB_ct fun _ _ h => h.1.1))))
  exact two_map (fun a => (⟨a.1, candOf a.1, a.1.L⟩ : TQD))
    (fun _ _ ⟨⟨h, _⟩, ha⟩ => ts_of h (of_decide_eq_true ha)) (tests_ct R)

/-- `mainQ` leaks the same from the same arguments, tape and table. -/
theorem mainQ_ct (R : RoundImpl) : RelCT isa (Two (MnB candOf pOk)) (mainQ R.name R.code) fun _ _ => True := by
  unfold mainQ
  refine RelCT.seq halve_ct (RelCT.seq prodSieve_ct (RelCT.seq (badLoad_ct (B := qOk))
    (two_ite' (fun a => decide (qOk a.1)) (fun _ _ h => h.2) ?_ (finMnB_ct fun _ _ h => h.1.1))))
  exact two_map (fun a => a) (fun _ _ h => h.1.1) (mainP_ct R)

/-- `main` leaks the same from the same arguments, tape and table. -/
theorem main_ct (R : RoundImpl) : RelCT isa (Two MnI) (main R.name R.code) fun _ _ => True := by
  unfold main
  refine RelCT.assoc (RelCT.seq mainA_ct (RelCT.seq residue_ct (RelCT.seq badLoad_ct
    (two_ite' (fun a => decide (goodRes a.1.g (candOf a.1))) (fun _ _ h => h.2) ?_
      (finMnB_ct fun _ _ h => h.1.1)))))
  refine RelCT.seq (two_map (fun a => a) (fun _ _ h => h.1.1) prodSieveN_ct)
    (RelCT.seq (badLoad_ct (B := pOk))
      (two_ite' (fun a => decide (pOk a.1)) (fun _ _ h => h.2) ?_ (finMnB_ct fun _ _ h => h.1.1)))
  exact two_map (fun a => a) (fun _ _ h => h.1.1) (mainQ_ct R)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on PPC64LE: constant time

`code_ct`: two runs with the same public arguments and tape (`qOf`), and
the same table's address, leak the same, whatever the registers they save. The entry loads `scratch_len`
from the stack, pinned once loaded; `zeroOut` and the length check load
`out`, `out_len` and the tape's length from the header, pinned once loaded;
the exit loads `scratch_len` from the header to find the save area.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

/-- A run's public data: its arguments and tape, without the registers it
saves. -/
def qOf (s : State) : PP := (ppOf s).with (fun _ => 0) 0

/-- On entry, with the public data `a`: the arguments and tape, and the
table's address. -/
def CI (a : PP × Addr) (s : State) : Prop :=
  pcPre s ∧ qOf s = a.1 ∧ s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = a.2

/-- `scratch_len` from the stack. -/
theorem entryL_ok {s : State} (hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) :
    WP isa (.block [.addSp .r11 96, .load .d .r12 .r11 0]) s fun t =>
      t.gpr .r12 = stackArg s 0 ∧ Keep [.r11, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [stackArgAddr, stackArg, Nat.reduceMul, Nat.reduceAdd] at hargs ⊢
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  prun [ea, hargs, BitVec.add_zero]

/-- The entry: the header's `out` and `out_len`. -/
theorem entry_ok (s : State) (h : pcPre s) :
    WP isa (.block entry) s fun t => Scr t (s.gpr .r10) (8 * (stackArg s 0).toNat) ∧ t.gpr .r31 = s.gpr .r10 ∧
      word t.mem (s.gpr .r10) 16 = s.gpr .r3 ∧ word t.mem (s.gpr .r10) 24 = s.gpr .r4 := by
  obtain ⟨hsp, hspT, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, nwS, hb1, hb2, hL, hg, hsw⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsw
  have hn : stackArg s 0 = BitVec.ofNat 64 (stackArg s 0).toNat := (ofNat_toNat _).symm
  have h8n : 160 ≤ 8 * (stackArg s 0).toNat := by omega
  have hscr : Scr s (s.gpr .r10) (8 * (stackArg s 0).toNat) :=
    Scr.of_mem (by rw [hwr, Nat.mul_comm]; simp) (by omega_using [nwS])
  have hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8 :=
    ⟨⟨stackArgAddr s 0, 8⟩, by rw [hrd]; simp, by simp [Region.Contains]⟩
  simp only [entry]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (entryA_ok rfl hn hargs h8n (hscr.st (by omega_using [h8n]))) fun tA ⟨⟨a11, _, _⟩, ka⟩ => ?_
  refine WP.mono (saves_ok (s₀ := tA) a11 h8n (by omega_using [nwS]) fun i hi => by
    rw [ka.wr]; exact hscr.st (by omega_using [h8n, hi])) fun tS hS => ?_
  have hS10 : tS.gpr .r10 = s.gpr .r10 := by rw [hS.gpr, ka.gpr _ (by decide)]
  refine WP.mono (header_ok (s := tS) hS10 fun d hd => by
    rw [hS.wr, ka.wr]; exact hscr.st (d := d) (by omega)) fun t₁ ⟨⟨c31, _, cm⟩, kc⟩ => ?_
  have gS : ∀ r, r ∉ ([.r0, .r11, .r12] : List Reg) → tS.gpr r = s.gpr r := fun r hr => by
    rw [hS.gpr]; exact ka.gpr r hr
  obtain ⟨-, w16, w24, -⟩ := hdrW_words tS.mem (s.gpr .r10) (tS.gpr .r12)
    (tS.gpr .r3) (tS.gpr .r4) (tS.gpr .r5) (tS.gpr .r6) (((tS.gpr .r7).setWidth 32).setWidth 64) (tS.gpr .r8)
    (tS.gpr .r9)
  rw [← cm] at w16 w24
  have hwr₁ : t₁.wr = s.wr := by rw [kc.wr, hS.wr, ka.wr]
  exact ⟨hscr.congr hwr₁, c31, w16.trans (gS _ (by decide)), w24.trans (gS _ (by decide))⟩

/-- After `scratch_len`'s load. -/
def EL (q : PP) (t : State) : Prop := t.gpr .r10 = q.B ∧ t.gpr .r12 = BitVec.ofNat 64 q.n

theorem pins_E1 : Pins EL [.r10, .r12] := by
  rintro q s₁ s₂ ⟨a10, a12⟩ ⟨b10, b12⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a10, b10]
  · rw [a12, b12]

/-- After the entry. -/
def Z0 (q : PP) (t : State) : Prop :=
  ∃ Z, Scr t q.B Z ∧ 32 ≤ Z ∧ t.gpr .r31 = q.B ∧ t.mem.readW (q.B + BitVec.ofNat 64 16) 64 = q.op ∧
    t.mem.readW (q.B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 q.L

theorem entry_ct : RelCT isa (Two fun q s => pcPre s ∧ qOf s = q) (.block entry) (Two Z0) := by
  refine two_post ?_ fun q s ⟨h, hq⟩ => ?_
  · rw [show entry = [.addSp .r11 96, .load .d .r12 .r11 0] ++ entry.drop 2 from rfl]
    refine RelCT.block_append (RelCT.seq (two_post (two_taint _ (pins_nil _) (by taint_decide)) (Ψ := EL)
      fun q s ⟨h, hq⟩ => ?_) (two_taint _ pins_E1 (by taint_decide)))
    subst hq
    have hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8 :=
      ⟨⟨stackArgAddr s 0, 8⟩, by rw [h.2.2.1]; simp, by simp [Region.Contains]⟩
    exact WP.mono (entryL_ok hargs) fun t ⟨t12, k⟩ => ⟨k.gpr _ (by decide), t12.trans (ofNat_toNat _).symm⟩
  · subst hq
    have h' := h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hb1, -, hL, -, hsw⟩ := h'
    have hL' : (s.gpr .r4).toNat = (qOf s).L := hL
    simp only [Spec.Rsa.scratchWords] at hsw
    refine WP.mono (entry_ok s h) fun t ⟨hs, h31, w16, w24⟩ => ⟨_, hs, by omega, h31, w16, ?_⟩
    rw [← hL']; exact w24.trans (ofNat_toNat _).symm

/-- With `out` and `out_len` loaded. -/
def Z1 (q : PP) (t : State) : Prop := t.gpr .r4 = q.op ∧ t.gpr .r5 = BitVec.ofNat 64 q.L

theorem pins_Z1 : Pins Z1 [.r4, .r5] := by
  rintro q s₁ s₂ ⟨a4, a5⟩ ⟨b4, b5⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a4, b4]
  · rw [a5, b5]

theorem zeroOut_ct : RelCT isa (Two Z0) zeroOut fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_post (two_taint _ (pins_r31 PP.B fun _ _ ⟨_, _, _, h31, _⟩ => h31) (by taint_decide))
    (Ψ := Z1) fun q s ⟨Z, hs, hZ, h31, hO, hL⟩ => ?_) (two_taint _ pins_Z1 (by taint_decide))
  exact WP.mono (WP.keep [.r0, .r4, .r5] (Q := fun s₂ => s₂.gpr .r4 = q.op ∧ s₂.gpr .r5 = BitVec.ofNat 64 q.L)
    (by simp only [ldh, hOut, hLen]
        prun [h31, hO, hL, hs.ld (d := 16) (n := 8) (by omega_using [hZ]), hs.ld (d := 24) (n := 8) (by omega_using [hZ])])
    (by decide)) fun _ ⟨h, _⟩ => h

/-- After the front. -/
def BI (a : PP × Addr) (t : State) : Prop :=
  ∃ sv toc, St (a.1.with sv toc) t ∧ word t.mem a.1.B 152 = BitVec.ofNat 64 a.1.L ∧ TabIn a.1.B a.1.Z a.2 t

theorem front_ct : RelCT isa (Two CI) (.seq (.block entry) zeroOut) (Two BI) :=
  two_post (two_map Prod.fst (fun _ _ ⟨h, hq, _⟩ => ⟨h, hq⟩) (RelCT.seq entry_ct zeroOut_ct))
    fun a s ⟨h, hq, ht⟩ => by
      obtain ⟨q, T⟩ := a
      dsimp only at hq ht
      subst hq ht
      exact WP.mono (front_tab s h) fun _ ⟨st, hU, htab⟩ => ⟨_, _, st, hU, htab⟩

/-- With the tape's length and `out_len` loaded. -/
def L34 (a : PP × Addr) (t : State) : Prop :=
  t.gpr .r3 = BitVec.ofNat 64 a.1.r.length ∧ t.gpr .r4 = BitVec.ofNat 64 a.1.L

theorem pins_L34 : Pins L34 [.r3, .r4] := by
  rintro q s₁ s₂ ⟨a3, a4⟩ ⟨b3, b4⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a3, b3]
  · rw [a4, b4]

/-- After the length check. -/
def LC (a : PP × Addr) (t : State) : Prop :=
  isa.eval (.zero .d .r5) t = some (decide ((if a.1.L ≤ a.1.r.length then 1 else 0) = 0)) ∧
    ∃ sv toc, St (a.1.with sv toc) t ∧ word t.mem a.1.B 152 = BitVec.ofNat 64 a.1.L ∧ TabIn a.1.B a.1.Z a.2 t

theorem lenChk_ct :
    RelCT isa (Two BI) (.block (([ldh .r3 hRandLen, ldh .r4 hLen] : List Instr) ++ geFlag .r5 .r3 .r4)) (Two LC) :=
  two_post (RelCT.block_append (RelCT.seq (two_post (two_taint _
      (pins_r31 (fun a : PP × Addr => a.1.B) fun _ _ ⟨_, _, h, _⟩ => h.r31) (by taint_decide)) (Ψ := L34)
        fun _ _ ⟨_, _, h, _⟩ => WP.mono (lenLoad_ok h) fun _ ⟨⟨a3, a4, _⟩, _⟩ => ⟨a3, a4⟩)
      (two_taint _ pins_L34 (by taint_decide))))
    fun _ _ ⟨sv, toc, h, hU, ht⟩ => WP.mono_syms (lenChk_ok h hU) fun _ ⟨he, st, hU', vm, vrd⟩ sy =>
      ⟨he, sv, toc, st, hU', ht.step sy (rs := []) (by rw [vm]; exact Frm.refl _ _ _) (by simp) vrd⟩

/-- Before the exit. -/
def XE (q : PP) (t : State) : Prop := ∃ sv toc, ESt (q.with sv toc) t

theorem body_ct (R : RoundImpl) : RelCT isa (Two BI) (.seq (.block (([ldh .r3 hRandLen, ldh .r4 hLen] : List Instr) ++
    geFlag .r5 .r3 .r4)) (.ite (.zero .d .r5) (.block (finish 0)) (main R.name R.code))) (Two fun (a : PP × Addr) => XE a.1) := by
  refine two_post (RelCT.seq lenChk_ct (two_ite' (fun a => decide ((if a.1.L ≤ a.1.r.length then 1 else 0) = 0))
    (fun _ _ h => h.1) ?_ ?_)) fun _ _ ⟨sv, toc, h, hU, ht⟩ => WP.mono (body_ok R h ht hU) fun _ h' => ⟨sv, toc, h'.1⟩
  · exact two_map Prod.fst (fun _ _ ⟨⟨_, _, _, h, _⟩, _⟩ => h.fs) (finish_ct (.inl rfl))
  · refine two_mono (fun (a : PP × Addr) _ ⟨⟨_, sv, toc, h, hU, ht⟩, hb⟩ => ⟨sv, toc, h, ht, hU, ?_⟩) (main_ct R)
    by_contra hc; simp only [decide_eq_false_iff_not] at hb; exact hb (by rw [ite_eq_right (by omega_using [hc])])

/-- With the save area's word count loaded. -/
def X1 (q : PP) (t : State) : Prop := t.gpr .r11 = BitVec.ofNat 64 q.n ∧ t.gpr .r31 = q.B

theorem pins_X1 : Pins X1 [.r11, .r31] := by
  rintro q s₁ s₂ ⟨a11, a31⟩ ⟨b11, b31⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a11, b11]
  · rw [a31, b31]

theorem exit_ct : RelCT isa (Two XE) (.block exit) fun _ _ => True := by
  rw [show exit = [ldh .r11 hWsLen] ++ exit.drop 1 from rfl]
  refine RelCT.block_append (RelCT.seq (two_post (two_taint _ (pins_r31 PP.B fun _ _ ⟨_, _, h⟩ => h.r31)
    (by taint_decide)) (Ψ := X1) fun q t ⟨sv, toc, h⟩ => ?_) (two_taint _ pins_X1 (by taint_decide)))
  have l0 : InRegions (t.rd ++ t.wr) ((q.with sv toc).B + BitVec.ofNat 64 0) 8 := h.scr.ld (d := 0) (by
    have := h.dims.n; simp only [PP.Z]; omega_using [this])
  exact WP.mono (WP.keep [.r11] (Q := fun u => u.gpr .r11 = BitVec.ofNat 64 (q.with sv toc).n)
    (by simp only [ldh, hWsLen]; prun [h.r31, l0, show t.mem.readW ((q.with sv toc).B + BitVec.ofNat 64 0) 64 =
      BitVec.ofNat 64 (q.with sv toc).n from h.len]) (by decide)) fun _ ⟨u11, k⟩ =>
    ⟨u11, (k.gpr _ (by decide)).trans h.r31⟩

/-- `vg_ffdh_parameter_candidate_sieved` leaks the same from the same public
arguments, tape and table. -/
theorem code_rel (R : RoundImpl) : RelCT isa (Two CI) (code R.name R.code) fun _ _ => True := by
  unfold code
  exact RelCT.assoc (RelCT.seq front_ct (RelCT.assoc (RelCT.seq (body_ct R)
    (two_map Prod.fst (fun _ _ h => h) exit_ct))))

theorem qOf_pub {s t : State} (h : pcPub s t) : qOf s = qOf t := by
  obtain ⟨hsp, hr, h3, -, h5, h6, h7, h8, -, h10, hst, -⟩ := h
  have hr' : pcRand s = pcRand t :=
    (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hr
  simp only [qOf, PP.with, ppOf, hsp, h3, h5, h6, h7, h8, h10, hst, hr']

/-- `vg_ffdh_parameter_candidate_sieved` in constant time, for any
implementation of the round. -/
theorem code_ct (R : RoundImpl) : ConstantTime isa pcContract.pre pcContract.pub (code R.name R.code) :=
  RelCT.constantTime ((code_rel R).mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨(qOf s, s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol), ⟨hs, rfl, rfl⟩,
      ⟨ht, (qOf_pub hp).symm, hp.2.2.2.2.2.2.2.2.2.2.2.symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-! # The verified parameter search (PPC64LE)

For any candidate using at most 176 bytes of stack (`search_verified_of`),
and for the candidate calling each shared Miller–Rabin round
(`search_verified`), as `Generic/MillerRabin/PPC64LE/Ffdh.lean` registers it.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Impl.MillerRabin.PPC64LE.Search (millerRabin draw round roundCall)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

theorem search_verified_of (c : Cand) :
    Verified target (Impl.Ffdh.PPC64LE.Generation.Search.code c.call)
      (Spec.Ffdh.sievedParameterSearchContract (abi.withConsts tables) stackUse) :=
  Verified.of_correct (search_correct c) (search_constantTime c) search_implies

theorem sdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : sdepth c = 0 := by
  induction c <;> simp_all [Code.noFrames, sdepth]

/-- The candidate uses the stack its round does. -/
theorem candidate_stack (v : RoundImpl) : sdepth (code v.name v.code) ≤ 176 := by
  simp only [code, main, mainQ, mainP, tests, testQ, testRest, test, millerRabin, draw, round, roundCall, pResult, qResult,
    ite_true, ite_false, Bool.false_eq_true, sdepth]
  simp (disch := decide) only [sdepth_of_noFrames, Nat.max_zero, Nat.zero_max, Nat.max_self]
  exact v.stack

/-- `vg_ffdh_parameter_candidate_sieved` calling the shared round `v`, as the
search calls it. -/
def Cand.ofRound (v : RoundImpl) : Cand where
  name := "vg_ffdh_parameter_candidate_sieved" ++ v.suffix
  code := Impl.Ffdh.PPC64LE.ParameterCandidate.code v.name v.code
  stack := candidate_stack v
  correct := ParameterCandidate.code_correct v
  ct := ParameterCandidate.code_ct v

/-- The search calling it. -/
abbrev searchCode (v : RoundImpl) : Prog isa := Impl.Ffdh.PPC64LE.Generation.Search.code (Cand.ofRound v).call

theorem search_verified (v : RoundImpl) :
    Verified target (searchCode v) (Spec.Ffdh.sievedParameterSearchContract (abi.withConsts tables) stackUse) :=
  search_verified_of (Cand.ofRound v)

end VG.Proof.Ffdh.PPC64LE.Generation
