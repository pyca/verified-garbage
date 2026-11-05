module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Cached
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
import VerifiedGarbage.Proof.Ffdh.CachedSat
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_ffdh_generate_key_precompute` on PPC64LE: the function

`vg_ffdh_generate_key_precompute(ctx = r3, ctx_len = r4, domain = r5,
domain_len = r6, p_len = r7, scratch = r8, scratch_len = r9)`, with the
vetted groups' table (`pcContract`), and the shared contract
(`pc_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation (tableSym tableConsts)

/-- The context's region. -/
abbrev pcCtx (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩

/-- The domain's region. -/
abbrev pcDomR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩

/-- The working space's region. -/
abbrev pcScr (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩

/-- The domain's bytes. -/
abbrev pcDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat

def pcPre (s : State) : Prop :=
  s.rd = [pcDomR s] ∧ s.wr = [pcCtx s, pcScr s] ∧ (pcCtx s).Disjoint (pcDomR s) ∧
    (pcCtx s).Disjoint (pcScr s) ∧ (pcDomR s).Disjoint (pcScr s) ∧
    (s.gpr .r3).toNat + (s.gpr .r4).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat * 8 ≤ 2 ^ 64 ∧
    Spec.Ffdh.pLenValid (s.gpr .r7).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .r7).toNat (s.gpr .r6).toNat ∧
    (s.gpr .r4).toNat = Spec.Ffdh.generationPrecomputedWords (s.gpr .r7).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .r7).toNat ≤ (s.gpr .r9).toNat ∧
    Spec.Ffdh.domainValid (s.gpr .r7).toNat (pcDom s)

def pcPost (s t : State) : Prop :=
  (t.gpr .r3).setWidth 32 = 1 ∧
    Spec.Ffdh.generationPrecompute (s.gpr .r7).toNat (pcDom s) = some (Spec.Rsa.wordsAt t.mem (s.gpr .r3) (s.gpr .r4).toNat)

def pcPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ (pcDom s₁).map (·.toNat) = (pcDom s₂).map (·.toNat) ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧
    s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9

/-- `vg_ffdh_generate_key_precompute`, with the vetted groups' table. -/
def pcContract : Contract isa where
  pre s := pcPre (stripConsts tableConsts s) ∧ ConstsOk tableConsts 0 s
  post := pcPost
  pub s₁ s₂ := pcPub s₁ s₂ ∧ s₁.syms tableSym = s₂.syms tableSym

theorem pc_pre0 {s : State} (h : (Spec.Ffdh.generationPrecomputeContract abi).pre s) : pcPre s := by
  sig_pre [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, abi, argRegs,
    List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] at h
  sig_split h
  sig_reduce [pcPre, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
  sig_and_intros
  sig_close
  all_goals first | with_reducible assumption | sig_disjoint_symm | omega

theorem pc_post0 {s t : State} (h : pcPost s t) : (Spec.Ffdh.generationPrecomputeContract abi).post s t := by
  sig_post [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, abi, argRegs,
    List.append_eq]
  sig_reduce [pcPost, pcDom] at h
  exact h

theorem pc_pub0 {s₁ s₂ : State} (h : (Spec.Ffdh.generationPrecomputeContract abi).pub s₁ s₂) : pcPub s₁ s₂ := by
  sig_pub [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, abi, argRegs,
    List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] at h
  exact h

/-! ## A caller meeting the contract -/

/-- The domain at `0x3000` and a table of `words` at `0x100000`. -/
private def pcSatMem (words : List (BitVec 64)) (a : Addr) : Byte :=
  if (a - 0x100000).toNat < 17744 then constMem 0x100000 words a else CachedSat.domainMem a

/-- The context at `0x200000`, the working space at `0x4000`. -/
private def pcSatState (words : List (BitVec 64)) : State where
  gpr r := match r with
    | .r3 => 0x200000 | .r4 => 275 | .r5 => 0x3000 | .r6 => 128 | .r7 => 64 | .r8 => 0x4000 | .r9 => 1056
    | _ => 0
  sp := 0x8000
  lr := 0
  mem := pcSatMem words
  rd := [⟨0x3000, 128⟩, ⟨0x100000, 17744⟩]
  wr := [⟨0x200000, 2200⟩, ⟨0x4000, 8448⟩]
  syms _ := 0x100000

private theorem pcSat_domain (words : List (BitVec 64)) :
    Spec.Rsa.bytesAt (pcSatState words).mem 0x3000 128 = CachedSat.domain := by
  apply CachedSat.bytesAt_eq
  intro i hi
  show pcSatMem words _ = _
  unfold pcSatMem
  apply ite_eq_right
  have : ∀ i < 128, ¬ ((0x3000 : BitVec 64) + BitVec.ofNat 64 i - 0x100000).toNat < 17744 := by decide
  exact this i hi

private theorem pcSat_pre (words : List (BitVec 64)) :
    (Spec.Ffdh.generationPrecomputeContract abi).pre (stripConsts [(tableSym, words)] (pcSatState words)) := by
  sig_pre [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, abi, argRegs,
    List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Rsa.scratchWords]
  refine ⟨rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, ?_⟩
  change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt (pcSatState words).mem 0x3000 128) = true
  rw [pcSat_domain]; exact CachedSat.domain_valid

private theorem pcGeometry :
    (0x100000 : Addr).toNat + 8 * 2218 ≤ 2 ^ 64 ∧
    (⟨0x100000, 8 * 2218⟩ : Region).Disjoint ⟨0x200000, 2200⟩ ∧
    (⟨0x100000, 8 * 2218⟩ : Region).Disjoint ⟨0x4000, 8448⟩ :=
  ⟨by decide, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩

private theorem pcSat_consts (words : List (BitVec 64)) (size : words.length = 2218) :
    ConstsOk [(tableSym, words)] 0 (pcSatState words) := by
  refine ⟨?_, ?_, ?_, fun r hr => ?_⟩
  · simp only [constRegs, Abi.constRegions, pcSatState, List.map_cons, List.map_nil, size]
    rfl
  · intro c hc i hi
    obtain rfl := List.mem_singleton.mp hc
    rw [← constMem_held 0x100000 words (by rw [size]; decide) i hi]
    apply Mem.readW_congr
    intro j hj
    show pcSatMem words _ = _
    unfold pcSatMem
    apply ite_eq_left
    have hi' : i < 2218 := by rw [← size]; exact hi
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    change ((0x100000 : BitVec 64) + BitVec.ofNat 64 (8 * i + j) - 0x100000).toNat < 17744
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
    obtain ⟨c, rfl, rfl⟩ := hr
    rw [size]
    refine ⟨pcGeometry.1, fun q hq => ?_, fun q hq => ?_⟩
    · change q ∈ ([⟨0x200000, 2200⟩, ⟨0x4000, 8448⟩] : List Region) at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact pcGeometry.2.1
      · exact pcGeometry.2.2
    · change q ∈ ([] : List Region) at hq
      contradiction
  · simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
    obtain ⟨c, rfl, rfl⟩ := hr
    exact (by decide : (0x100000 : BitVec 64).toNat % 64 = 0)

private theorem pcSatAux (words : List (BitVec 64)) (size : words.length = 2218) :
    ∃ s, (Spec.Ffdh.generationPrecomputeContract (abi.withConsts [(tableSym, words)])).pre s :=
  ⟨pcSatState words, pre_consts.mpr ⟨pcSat_pre words, pcSat_consts words size⟩⟩

theorem precompute_sat : ∃ s, (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts)).pre s :=
  pcSatAux VG.Impl.Ffdh.VettedGroups.tableWords VG.Proof.Ffdh.VettedTableFacts.tableWords_length

theorem pc_implies : pcContract.Implies (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts)) where
  pre s h := by
    obtain ⟨hp, hc⟩ := pre_consts.mp h
    exact ⟨pc_pre0 hp, hc⟩
  post _ _ _ h := post_consts.mpr (pc_post0 h)
  pub _ _ _ _ h := ⟨pc_pub0 (pub_consts.mp h).1, (pub_consts.mp h).2 _ List.mem_cons_self⟩
  sat := precompute_sat

end VG.Proof.Ffdh.PPC64LE.Cached
