module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Search.Data
public import VerifiedGarbage.Impl.Ffdh.RISCV64.Generation.Search
public import VerifiedGarbage.Spec.Ffdh.SievedContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Verified
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Search.Correct
import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Search.CT
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-! # The verified parameter search (RISC-V)

`searchContract` states the shared contract on the registers and the stack:
under `abi` for the state without RSA's table of trial division
(`search_implies_pre₀` and the others, with `basePre` the precondition but
the table's), then under `abi.withConsts tables` (`pre_consts`,
`post_consts`, `pub_consts`), whose `ConstsOk` gives the table's region and
entries (`search_implies`). With correctness (`search_correct`) and constant
time (`search_constantTime`), the search is verified for any candidate
proven against `vg_ffdh_parameter_candidate_sieved`'s contract with 96 bytes
of stack (`search_verified_of`), with 128 bytes of its own; and for the
candidate calling each shared Miller–Rabin round (`search_verified`), as
`Generic/MillerRabin/RISCV64/Ffdh.lean` registers it.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Generation

open VG VG.RISCV64 VG.Spec.Ffdh

/-- The buffers the controller only reads, but the table. -/
def inReads₀ (s : State) : List Region := [inRand s, inArgs s]

/-- The precondition without the table. -/
def basePre (S : Nat) (s : State) : Prop :=
  s.sp.toNat + 8 * 2 ≤ 2 ^ 64 ∧ stackUse S ≤ s.sp.toNat ∧ s.sp.toNat % 16 = 0 ∧
    s.rd = inReads₀ s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads₀ s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads₀ s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads₀ s, (below s.sp (stackUse S)).Disjoint r) ∧
    (s.gpr .a2).toNat % 8 = 0 ∧ (s.gpr .a7).toNat % 8 = 0 ∧ (stackArg s 1).toNat % 8 = 0 ∧
    512 ≤ genBits s ∧ genBits s ≤ 8192 ∧ genLen s = (genBits s + 7) / 8 ∧
    (genGen s = 2 ∨ genGen s = 5) ∧
    Spec.Rsa.scratchWords (genLen s) ≤ (stackArg s 0).toNat ∧
    genAttempts s ≤ parameterAttempts (genBits s) ∧
    s.mem.readW (stackArg s 1 + 8) 64 = BitVec.ofNat 64 (genLen s) ∧
    s.mem.readW (stackArg s 1 + 16) 64 = BitVec.ofNat 64 (parameterEntropy (genBits s)) ∧
    (s.gpr .a6).toNat ≤ parameterEntropy (genBits s)

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

private theorem args_nowrap {s : State} (h : s.sp.toNat + 8 * 2 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 16 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  omega

theorem search_implies_pre₀ (S : Nat) (s : State) (h : (sievedParameterSearchContract abi (stackUse S)).pre s) :
    basePre S s := by
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

theorem search_implies_post₀ (S : Nat) : ∀ s t, True → searchPost s t →
    (sievedParameterSearchContract abi (stackUse S)).post s t := by
  sig_implies_post [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, searchPost,
    searchResult, genRand, genLen, genBits, genGen, genAttempts, stackArgs_two, List.append_eq,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_implies_pub₀ (S : Nat) (s t : State) (h : (sievedParameterSearchContract abi (stackUse S)).pub s t) :
    s.sp = t.sp ∧ (genRand s).map (·.toNat) = (genRand t).map (·.toNat) ∧
    Spec.Rsa.wordsAt s.mem (stackArg s 1) 4 = Spec.Rsa.wordsAt t.mem (stackArg t 1) 4 ∧
    s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1 ∧ s.gpr .a2 = t.gpr .a2 ∧ s.gpr .a3 = t.gpr .a3 ∧
    (s.gpr .a4).setWidth 32 = (t.gpr .a4).setWidth 32 ∧ s.gpr .a5 = t.gpr .a5 ∧ s.gpr .a6 = t.gpr .a6 ∧
    s.gpr .a7 = t.gpr .a7 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1 := by
  sig_pub [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackArgs_two, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1⟩ := h
  have hl1 : (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)).length =
      (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt t.mem (t.gpr .a5) (t.gpr .a6).toNat)).length := by
    simp only [List.length_map, Spec.Rsa.bytesAt, List.length_range, r6]
  obtain ⟨hr, hw⟩ := List.append_inj hleak hl1
  exact ⟨hsp, hr, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, r0, r1, r2, r3, r4, r5, r6, r7,
    a0, a1⟩

private theorem tables_eq' :
    tables = [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)] := rfl

private theorem packed_length' : Impl.RsaKeyGen.TrialTable32.packed.length = 1024 :=
  Proof.RsaKeyGen.TrialTable32.packed_length

private theorem tab_regs (s : State) : constRegs tables s = [inTab s] := by
  rw [tables_eq', constRegs, Abi.constRegions_cons, Abi.constRegions_nil, packed_length']; rfl

/-- The precondition without the table, and what the table adds, are the
controller's. -/
theorem pre_of_base (S : Nat) (s : State) (hb : basePre S (stripConsts tables s))
    (hc : ConstsOk tables (stackUse S) s) : searchPre S s := by
  obtain ⟨a1, a2, a3, hrd, hwr, hnw, hpw, hwrd, hstk, al1, al2, al3, b1, b2, l, g, sc, at', w8, w16, r6⟩ := hb
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
  refine ⟨a1, a2, a3, hrd₂, hwr', fun r hr => ?_, hpw, fun w hw r hr => ?_, fun r hr => ?_, al1, al2, al3,
    b1, b2, l, g, sc, at', w8, w16, r6, ?_, fun i hi => ?_⟩
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
    · refine (ht.2.2 _ ?_).symm
      simp only [abi, stackUse, stackBelow, below, List.mem_singleton]
  · exact hc.2.2.2 (inTab s) (by rw [tab_regs]; exact List.mem_singleton_self _)
  · have hm : (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed) ∈ tables :=
      List.mem_singleton_self _
    have e := hc.readW hm (by rw [packed_length']; exact hi)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [packed_length']; exact hi), Option.getD_some,
      Proof.RsaKeyGen.TrialTable32.packed_entry hi] at e
    exact e

theorem search_implies_pre (S : Nat) (s : State)
    (h : (sievedParameterSearchContract (abi.withConsts tables) (stackUse S)).pre s) : (searchContract S).pre s := by
  unfold sievedParameterSearchContract at h
  rw [tables_eq'] at h
  obtain ⟨h₁, h₂⟩ := pre_consts.mp h
  exact pre_of_base S s (search_implies_pre₀ S _ h₁) h₂

theorem search_implies_post (S : Nat) (s t : State)
    (_ : (sievedParameterSearchContract (abi.withConsts tables) (stackUse S)).pre s)
    (h : (searchContract S).post s t) :
    (sievedParameterSearchContract (abi.withConsts tables) (stackUse S)).post s t := by
  unfold sievedParameterSearchContract
  rw [tables_eq']
  exact post_consts.mpr (search_implies_post₀ S s t trivial h)

theorem search_implies_pub (S : Nat) (s t : State)
    (_ : (sievedParameterSearchContract (abi.withConsts tables) (stackUse S)).pre s)
    (_ : (sievedParameterSearchContract (abi.withConsts tables) (stackUse S)).pre t)
    (h : (sievedParameterSearchContract (abi.withConsts tables) (stackUse S)).pub s t) :
    (searchContract S).pub s t := by
  unfold sievedParameterSearchContract at h
  rw [tables_eq'] at h
  obtain ⟨hp, hsy⟩ := pub_consts.mp h
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l, m, n⟩ := search_implies_pub₀ S s t hp
  exact ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, hsy _ (List.mem_singleton_self _)⟩

/-! ## A state satisfying the precondition -/

/-- The stack arguments, `scratch_len` 1056 and the state at `0x200000`, at
`0x100000`; the state's words 0, 64 and the entropy cap of 512 bits. -/
def satSmall : Mem := fun a =>
  if a = 0x100000 then 0x20 else if a = 0x100001 then 0x04 else if a = 0x10000A then 0x20
  else if a = 0x200008 then 0x40 else if a = 0x200010 then 0x40 else if a = 0x200012 then 0x20 else 0

/-- The witness's memory: the small words, and the table at `0x800000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def satMem : Mem := fun a =>
  if (a - 0x100000).toNat < 0x200000 then satSmall a else constMem 0x800000 Impl.RsaKeyGen.TrialTable32.packed a

theorem satMem_held : ∀ i < Impl.RsaKeyGen.TrialTable32.packed.length,
    satMem.readW (0x800000 + BitVec.ofNat 64 (8 * i)) 64 = Impl.RsaKeyGen.TrialTable32.packed.getD i 0 := by
  intro i hi
  rw [← constMem_held _ _ (by rw [packed_length']; decide) i hi]
  refine Mem.readW_congr fun j hj => ?_
  have hn : ¬ (0x800000 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000 : Addr).toNat < 0x200000 := by
    rw [packed_length'] at hi
    simp only [Nat.reduceDiv] at hj
    have h1 : (0x800000 : Addr).toNat = 8388608 := rfl
    have h2 : (0x100000 : Addr).toNat = 1048576 := rfl
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h1, h2]
    omega
  unfold satMem
  simp only [hn, ↓reduceIte]

theorem satMem_small (a : Addr) (ha : (a - 0x100000).toNat + 8 ≤ 0x200000) :
    satMem.readW a 64 = satSmall.readW a 64 := by
  refine Mem.readW_congr fun j hj => ?_
  have hn : (a + BitVec.ofNat 64 j - 0x100000 : Addr).toNat < 0x200000 := by
    simp only [Nat.reduceDiv] at hj
    have h2 : (0x100000 : Addr).toNat = 1048576 := rfl
    have := a.isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h2] at ha ⊢
    omega
  unfold satMem
  simp only [hn, ↓reduceIte]

/-- A 512-bit search with an empty tape, its buffers above the stack, and
the table. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x300000 | .a1 => 64 | .a2 => 0x400000 | .a3 => 512 | .a4 => 2 | .a5 => 0x500000
    | .a7 => 0x600000 | _ => 0
  sp := 0x100000
  mem := satMem
  rd := [⟨0x500000, 0⟩, ⟨0x100000, 16⟩, ⟨0x800000, 8192⟩]
  wr := [⟨0x300000, 64⟩, ⟨0x400000, 8⟩, ⟨0x600000, 1056 * 8⟩, ⟨0x200000, 128⟩]
  syms _ := 0x800000

theorem sat_arg (i : Nat) (hi : i < 2) :
    stackArg satState i = satSmall.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 := by
  refine satMem_small _ ?_
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> decide

theorem sat_arg0 : stackArg satState 0 = 0x420 := (sat_arg 0 (by decide)).trans (by decide)
theorem sat_arg1 : stackArg satState 1 = 0x200000 := (sat_arg 1 (by decide)).trans (by decide)
theorem sat_w0 : satMem.readW 0x200000 64 = 0 := (satMem_small _ (by decide)).trans (by decide)
theorem sat_w8 : satMem.readW (0x200000 + 8) 64 = 64 := (satMem_small _ (by decide)).trans (by decide)
theorem sat_w16 : satMem.readW (0x200000 + 16) 64 = BitVec.ofNat 64 (parameterEntropy 512) :=
  (satMem_small _ (by decide)).trans (by decide)

theorem sat_base : (sievedParameterSearchContract abi (stackUse 96)).pre (stripConsts tables satState) := by
  have a0 : stackArg (stripConsts tables satState) 0 = 0x420 := sat_arg0
  have a1 : stackArg (stripConsts tables satState) 1 = 0x200000 := sat_arg1
  have w0 : (stripConsts tables satState).mem.readW 0x200000 64 = 0 := sat_w0
  have w8 : (stripConsts tables satState).mem.readW (0x200000 + 8) 64 = 64 := sat_w8
  have w16 : (stripConsts tables satState).mem.readW (0x200000 + 16) 64 =
      BitVec.ofNat 64 (parameterEntropy 512) := sat_w16
  unfold sievedParameterSearchContract
  refine Sig.contract_pre_of_check (by decide +kernel) ?_
  sig_reduce [parameterSearchSig, abi, argRegs, stackArgs_two, List.append_eq, a0, a1, w0, w8, w16,
    parameterAttempts, parameterEntropy]
  sig_and_intros
  all_goals first
    | trivial
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel

theorem sat_consts : ConstsOk tables (stackUse 96) satState := by
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
    · change r ∈ [⟨0x300000, 64⟩, ⟨0x400000, 8⟩, ⟨0x600000, 1056 * 8⟩, ⟨0x200000, 128⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · change r ∈ stackBelow 0x100000 (stackUse 96) at hr
      simp only [stackBelow, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact Region.disjoint_of_sep (by decide)
  · rw [constRegs, Abi.constRegions_cons, Abi.constRegions_nil, hl]
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    decide

theorem sat : (sievedParameterSearchContract (abi.withConsts tables) (stackUse 96)).pre satState := by
  unfold sievedParameterSearchContract
  rw [tables_eq']
  have h₁ := sat_base
  have h₂ := sat_consts
  unfold sievedParameterSearchContract at h₁
  rw [tables_eq'] at h₁ h₂
  exact pre_consts.mpr ⟨h₁, h₂⟩

theorem search_implies : (searchContract 96).Implies
    (sievedParameterSearchContract (abi.withConsts tables) (stackUse 96)) where
  pre := search_implies_pre 96
  post := search_implies_post 96
  pub := search_implies_pub 96
  sat := ⟨satState, sat⟩

theorem search_verified_of (c : Cand) (hS : c.S = 96) :
    Verified target (Impl.Ffdh.RISCV64.Generation.Search.code c.call)
      (sievedParameterSearchContract (abi.withConsts tables) (stackUse 96)) := by
  have hc := search_correct c
  have hct := search_constantTime c
  rw [hS] at hc hct
  exact Verified.of_correct hc hct search_implies

/-- `vg_ffdh_parameter_candidate_sieved` calling the shared round `v`, as the
search calls it, with the round's 96 bytes of stack. -/
def Cand.ofRound (v : Proof.MillerRabin.RISCV64.RoundImpl) : Cand where
  name := "vg_ffdh_parameter_candidate_sieved" ++ v.suffix
  code := ParameterCandidate.candCode v
  S := 96
  pos := by decide
  small := by decide
  stack := ParameterCandidate.candidate_stack v
  correct := ParameterCandidate.candidate_correct v
  ct := ParameterCandidate.candidate_ct v

/-- The search calling it. -/
abbrev searchCode (v : Proof.MillerRabin.RISCV64.RoundImpl) : Prog isa :=
  Impl.Ffdh.RISCV64.Generation.Search.code (Cand.ofRound v).call

theorem search_verified (v : Proof.MillerRabin.RISCV64.RoundImpl) :
    Verified target (searchCode v) (sievedParameterSearchContract (abi.withConsts tables) 128) :=
  search_verified_of (Cand.ofRound v) rfl

end VG.Proof.Ffdh.RISCV64.Generation
