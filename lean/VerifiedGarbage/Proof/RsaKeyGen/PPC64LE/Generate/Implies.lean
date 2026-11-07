module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Generate.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
meta import VerifiedGarbage.Proof.Framework.Contract

-- separate module: its proofs build in parallel with those of `Correct` and `CT`, which `Verified` also imports

/-! # The controller's contract is its shared callable contract (PPC64LE)

Under `abi` for the state without the table (`gen_implies_pre₀` and the
others), then under `abi.withConsts tables`, as for the prime search
(`Proof/RsaKeyGen/PPC64LE/Search/Implies.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Generate

open VG VG.PPC64LE VG.Spec.RsaKeyGen

theorem gen_implies_pre₀ (s : State) (h : (keySearchContract abi stackUse).pre s) : basePre s := by
  sig_pre [keySearchContract, keySearchSig, abi, argRegs, stackBelow, basePre,
    inReads, inWrites, inKey, inUsed, inRand, inScr, inState, List.append_eq] at h
  sig_pre [keySearchContract, keySearchSig, abi, argRegs, stackBelow, basePre,
    inReads, inWrites, inKey, inUsed, inRand, inScr, inState, List.append_eq] at h
  sig_split h
  sig_reduce [keySearchContract, keySearchSig, abi, argRegs, stackBelow, basePre,
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

theorem gen_implies_post₀ : ∀ s t, True → genPost s t → (keySearchContract abi stackUse).post s t := by
  intro s t _ h
  sig_post [keySearchContract, keySearchSig, abi, argRegs, genPost,
    genResult, genRand, genE, genLen, genProgress, List.append_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [genPost, genResult, genRand, genE, genLen, genProgress, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact h

theorem gen_implies_pub₀ (s t : State) (h : (keySearchContract abi stackUse).pub s t) :
    s.sp = t.sp ∧
    s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r5 = t.gpr .r5 ∧ s.gpr .r6 = t.gpr .r6 ∧
    s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9 ∧ s.gpr .r10 = t.gpr .r10 ∧
    Spec.Rsa.wordsAt s.mem (s.gpr .r10) 7 = Spec.Rsa.wordsAt t.mem (t.gpr .r10) 7 ∧
    (genResult s).keyStatus = (genResult t).keyStatus ∧ (genResult s).used = (genResult t).used ∧
    (genResult s).available = (genResult t).available ∧ (genResult s).trace = (genResult t).trace := by
  sig_pub [keySearchContract, keySearchSig, abi, argRegs, List.append_eq] at h
  obtain ⟨hsp, hleak, r3, r4, r5, r6, r7, r8, r9, r10⟩ := h
  have hl : (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt s.mem (s.gpr .r10) 7)).length =
      (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt t.mem (t.gpr .r10) 7)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range]
  obtain ⟨hab, htr⟩ := List.append_inj hleak (by simp only [List.length_append, hl, List.length_cons,
    List.length_nil])
  obtain ⟨hw, hc⟩ := List.append_inj hab hl
  simp only [List.cons.injEq, and_true] at hc
  exact ⟨hsp, r3, r4, r5, r6, r7, r8, r9, r10,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, hc.1, hc.2.1, hc.2.2, htr⟩

private theorem tables_eq' :
    tables = [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)] := rfl

theorem gen_implies_pre (s : State)
    (h : (keySearchContract (abi.withConsts tables) stackUse).pre s) : genContract.pre s := by
  unfold keySearchContract at h
  rw [tables_eq'] at h
  obtain ⟨h₁, h₂⟩ := pre_consts.mp h
  exact ⟨gen_implies_pre₀ _ h₁, h₂⟩

theorem gen_implies_post (s t : State) (_ : (keySearchContract (abi.withConsts tables) stackUse).pre s)
    (h : genContract.post s t) : (keySearchContract (abi.withConsts tables) stackUse).post s t := by
  unfold keySearchContract
  rw [tables_eq']
  exact post_consts.mpr (gen_implies_post₀ s t trivial h)

theorem gen_implies_pub (s t : State) (_ : (keySearchContract (abi.withConsts tables) stackUse).pre s)
    (_ : (keySearchContract (abi.withConsts tables) stackUse).pre t)
    (h : (keySearchContract (abi.withConsts tables) stackUse).pub s t) : genContract.pub s t := by
  unfold keySearchContract at h
  rw [tables_eq'] at h
  obtain ⟨hp, hsy⟩ := pub_consts.mp h
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o⟩ := gen_implies_pub₀ s t hp
  exact ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o, hsy _ (List.mem_singleton_self _)⟩

/-! ## A state satisfying the precondition -/

private theorem packed_length' : Impl.RsaKeyGen.TrialTable32.packed.length = 1024 :=
  Proof.RsaKeyGen.TrialTable32.packed_length

/-- The state's words at `0x4000`: 0, 32 and `32769 · 32`. -/
def satSmall : Mem := fun a =>
  if a = 0x4008 then 0x20 else if a = 0x4010 then 0x20 else if a = 0x4012 then 0x10 else 0

/-- The witness's memory: the small words, and the table at `0x20000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def satMem : Mem := fun a =>
  if (a - 0x4000).toNat < 0x4080 then satSmall a else constMem 0x20000 Impl.RsaKeyGen.TrialTable32.packed a

theorem satMem_held : ∀ i < Impl.RsaKeyGen.TrialTable32.packed.length,
    satMem.readW (0x20000 + BitVec.ofNat 64 (8 * i)) 64 = Impl.RsaKeyGen.TrialTable32.packed.getD i 0 := by
  intro i hi
  rw [← constMem_held _ _ (by rw [packed_length']; decide) i hi]
  refine Mem.readW_congr fun j hj => ?_
  have hn : ¬ (0x20000 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x4000 : Addr).toNat < 0x4080 := by
    rw [packed_length'] at hi
    simp only [Nat.reduceDiv] at hj
    have h1 : (0x20000 : Addr).toNat = 131072 := rfl
    have h2 : (0x4000 : Addr).toNat = 16384 := rfl
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h1, h2]
    omega
  unfold satMem
  simp only [hn, ↓reduceIte]

theorem satMem_small (a : Addr) (ha : (a - 0x4000).toNat + 8 ≤ 0x4080) :
    satMem.readW a 64 = satSmall.readW a 64 := by
  refine Mem.readW_congr fun j hj => ?_
  have hn : (a + BitVec.ofNat 64 j - 0x4000 : Addr).toNat < 0x4080 := by
    simp only [Nat.reduceDiv] at hj
    have h2 : (0x4000 : Addr).toNat = 16384 := rfl
    have := a.isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h2] at ha ⊢
    omega
  unfold satMem
  simp only [hn, ↓reduceIte]

/-- Primes of 32 octets, an empty tape, disjoint buffers, the state's words
for the width at `0x4000`, and the table. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 288 | .r5 => 0x2000 | .r6 => 0x3000 | .r7 => 0 | .r8 => 0x10000
    | .r9 => 1056 | .r10 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem := satMem
  rd := [⟨0x3000, 0⟩, ⟨0x20000, 8192⟩]
  wr := [⟨0x1000, 288⟩, ⟨0x2000, 8⟩, ⟨0x10000, 1056 * 8⟩, ⟨0x4000, 56⟩]
  syms _ := 0x20000

theorem sat_w0 : satMem.readW 0x4000 64 = 0 := (satMem_small _ (by decide)).trans (by decide)
theorem sat_w8 : satMem.readW (0x4000 + 8) 64 = 32 := (satMem_small _ (by decide)).trans (by decide)
theorem sat_w16 : satMem.readW (0x4000 + 16) 64 = BitVec.ofNat 64 (primeEntropy 32) :=
  (satMem_small _ (by decide)).trans (by decide)
theorem sat_w32 : satMem.readW (0x4000 + 32) 64 = 0 := (satMem_small _ (by decide)).trans (by decide)

theorem sat_e : Spec.Rsa.bytesAt satMem (0x4000 + 48) 8 = List.replicate 8 0 := by
  have hb : ∀ j < 8, satMem (0x4000 + 48 + BitVec.ofNat 64 j) = 0 := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      h | h | h | h | h | h | h | h <;> subst h <;> (unfold satMem; decide)
  simp only [Spec.Rsa.bytesAt]
  refine List.eq_replicate_iff.mpr ⟨by simp, fun b hm => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
  exact hb j (List.mem_range.mp hj)

theorem sat_base : (keySearchContract abi stackUse).pre (stripConsts tables satState) := by
  have w0 : (stripConsts tables satState).mem.readW 0x4000 64 = 0 := sat_w0
  have w8 : (stripConsts tables satState).mem.readW (0x4000 + 8) 64 = 32 := sat_w8
  have w16 : (stripConsts tables satState).mem.readW (0x4000 + 16) 64 = BitVec.ofNat 64 (primeEntropy 32) :=
    sat_w16
  have w32 : (stripConsts tables satState).mem.readW (0x4000 + 32) 64 = 0 := sat_w32
  have we : Spec.Rsa.bytesAt (stripConsts tables satState).mem (0x4000 + 48) 8 = List.replicate 8 0 := sat_e
  unfold keySearchContract
  refine Sig.contract_pre_of_check (by decide +kernel) ?_
  sig_reduce [keySearchSig, abi, argRegs, List.append_eq, w0, w8, w16, w32, we, primeLenValid]
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
    · change r ∈ [⟨0x1000, 288⟩, ⟨0x2000, 8⟩, ⟨0x10000, 1056 * 8⟩, ⟨0x4000, 56⟩] at hr
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

theorem sat : (keySearchContract (abi.withConsts tables) stackUse).pre satState := by
  unfold keySearchContract
  rw [tables_eq']
  have h₁ := sat_base
  have h₂ := sat_consts
  unfold keySearchContract at h₁
  rw [tables_eq'] at h₁ h₂
  exact pre_consts.mpr ⟨h₁, h₂⟩

theorem gen_implies : genContract.Implies (keySearchContract (abi.withConsts tables) stackUse) where
  pre := gen_implies_pre
  post := gen_implies_post
  pub := gen_implies_pub
  sat := ⟨satState, sat⟩

end VG.Proof.RsaKeyGen.PPC64LE.Generate
