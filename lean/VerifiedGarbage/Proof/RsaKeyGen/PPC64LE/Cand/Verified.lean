module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTTop
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig

/-!
# `vg_rsa_keygen_candidate` on PPC64LE: verified, given trial division

`cand_verified`: the code, with any trial division `trial` that meets
`DivOk` and any implementation `R` of the Miller–Rabin round, meets
`candidateContract` with the table of trial division (`TrialTable32`) and
400 bytes of stack: 48 for its push, 176 for its frame and 176 for the
round's frames.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont
open VG.Impl.RsaKeyGen (TrialTable32.symbol TrialTable32.packed TrialTable32.consts)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

theorem packed_length : TrialTable32.packed.length = 1024 := by
  simp [TrialTable32.packed]

theorem consts_eq : TrialTable32.consts = [(TrialTable32.symbol, TrialTable32.packed)] := rfl

/-- The contract, with the table. -/
abbrev contract : Contract isa := Spec.RsaKeyGen.candidateContract (abi.withConsts TrialTable32.consts) 400

theorem cin_strip {s : State} (h : CIn (stripConsts TrialTable32.consts s)) : CIn s :=
  ⟨h.spLo, h.spHi, List.mem_of_mem_take h.rE, List.mem_of_mem_take h.rP, List.mem_of_mem_take h.rR,
    List.mem_of_mem_take h.rA, h.wr, h.oU, h.oE, h.oP, h.oR, h.oS, h.oA, h.uE, h.uP, h.uR, h.uS, h.uA, h.eS, h.pS,
    h.rS, h.SA, h.Fo, h.Fu, h.Fe, h.Fp, h.Fr, h.FS, h.FA, h.fo, h.fu, h.fe, h.fp, h.fr, h.fS, h.valid, h.el1, h.el2,
    h.plv, h.scr⟩

theorem tab_of {s : State} (hc : CIn s) (h : ConstsOk TrialTable32.consts 400 s) : TabOk s := by
  have hm : (TrialTable32.symbol, TrialTable32.packed) ∈ TrialTable32.consts := by rw [consts_eq]; simp
  have hreg : (⟨s.syms TrialTable32.symbol, 8 * 1024⟩ : Region) ∈ constRegs TrialTable32.consts s := by
    rw [consts_eq, constRegs, Abi.constRegions_cons, Abi.constRegions_nil, packed_length]; simp
  have hw := (h.2.2.1 _ hreg).2.1
  have hr := (h.2.2.1 _ hreg).2.2
  refine ⟨packed_length ▸ h.fit hm, packed_length ▸ h.mem_rd hm, fun i hi => h.readW hm (by rw [packed_length]; exact hi),
    fun ρ hρ => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl
  · exact hw _ (by rw [hc.wr]; simp)
  · exact hw _ (by rw [hc.wr]; simp)
  · exact hw _ (by rw [hc.wr]; simp)
  · exact hr _ (by simp [abi, stackBelow, cF, below])

theorem pre_facts {s : State} (h : contract.pre s) : CIn s ∧ TabOk s := by
  unfold contract Spec.RsaKeyGen.candidateContract at h
  rw [consts_eq] at h
  obtain ⟨h₁, h₂⟩ := pre_consts.mp h
  have hc := cin_strip (cin_of_pre _ h₁)
  exact ⟨hc, tab_of hc (consts_eq ▸ h₂)⟩

theorem post_of {s s' : State} (hq : CQ s (s'.gpr .r3) s'.mem) : contract.post s s' := by
  unfold contract Spec.RsaKeyGen.candidateContract
  rw [consts_eq]
  refine post_consts.mpr ?_
  sig_post [Spec.RsaKeyGen.candidateSig, abi, argRegs, stackArgs_three, List.append_eq]
  obtain ⟨h1, h2, h3⟩ := hq
  refine ⟨?_, h2, h3⟩
  have hs : Spec.RsaKeyGen.candidateStatus (cOp s) < 4 := by
    unfold Spec.RsaKeyGen.candidateStatus
    split <;> decide
  rw [BitVec.toNat_setWidth, h1, Nat.mod_eq_of_lt (by omega)]
  rfl

theorem pub_of {s₁ s₂ : State} (hp : contract.pub s₁ s₂) : s₁.sp = s₂.sp ∧ pubOf s₁ = pubOf s₂ := by
  unfold contract Spec.RsaKeyGen.candidateContract at hp
  rw [consts_eq] at hp
  obtain ⟨hp, hsy⟩ := pub_consts.mp hp
  sig_pub [Spec.RsaKeyGen.candidateSig, abi, argRegs, stackArgs_three, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  obtain ⟨hsp, hl, r3, r4, r5, r6, r7, r8, r9, r10, a0, a1, a2⟩ := hp
  have hlen : (List.map (fun x => BitVec.toNat x) (eB s₁)).length =
      (List.map (fun x => BitVec.toNat x) (eB s₂)).length := by
    simp only [List.length_map, bytesAt_length, r7]
  obtain ⟨he, hk⟩ := List.append_inj hl hlen
  refine ⟨hsp, ?_⟩
  unfold pubOf
  congr 1
  all_goals first
    | exact hk
    | exact VG.Proof.RsaKeyGen.map_toNat_inj he
    | exact hsy _ (List.mem_singleton_self _)
    | rw [stackArgs_three, stackArgs_three, a0, a1, a2]
    | simp [argRegs, r3, r4, r5, r6, r7, r8, r9, r10]

theorem cand_correct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) :
    ∀ s, contract.pre s → ∃ t s', Exec isa (VG.Impl.RsaKeyGen.PPC64LE.Candidate.code trial R.name R.code) s t s' ∧
      abiPreserved s s' ∧ contract.post s s' := by
  intro s h
  obtain ⟨hc, ht⟩ := pre_facts h
  obtain ⟨t, s', he, ha, hq⟩ := code_correct D R hc ht
  exact ⟨t, s', he, ha, post_of hq⟩

theorem cand_ct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) :
    ConstantTime isa contract.pre contract.pub (VG.Impl.RsaKeyGen.PPC64LE.Candidate.code trial R.name R.code) :=
  RelCT.constantTime ((code_ct D R).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨pubOf s₁, ⟨(pre_facts h₁).1, (pre_facts h₁).2, rfl⟩, ⟨(pre_facts h₂).1, (pre_facts h₂).2, (pub_of hp).2.symm⟩,
      (pub_of hp).1⟩) fun _ _ h => h)

/-- The stack arguments of the witness: `rand_len` 0, `scratch` at
`0x10000`, `scratch_len` 544, at `0x8060`. -/
def satStk : Mem := fun a => if a = 0x806A then 1 else if a = 0x8070 then 0x20 else if a = 0x8071 then 2 else 0

/-- The witness's memory: its stack arguments, and the table at `0x20000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def satMem : Mem := fun a =>
  if (a - 0x8060).toNat < 24 then satStk a else constMem 0x20000 TrialTable32.packed a

theorem satMem_held : ∀ i < TrialTable32.packed.length,
    satMem.readW (0x20000 + BitVec.ofNat 64 (8 * i)) 64 = TrialTable32.packed.getD i 0 := by
  intro i hi
  rw [← constMem_held _ _ (by rw [packed_length]; decide) i hi]
  refine Mem.readW_congr fun j hj => ?_
  have hn : ¬ (0x20000 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x8060 : Addr).toNat < 24 := by
    rw [packed_length] at hi
    simp only [Nat.reduceDiv] at hj
    have h1 : (0x20000 : Addr).toNat = 131072 := rfl
    have h2 : (0x8060 : Addr).toNat = 32864 := rfl
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h1, h2]
    omega
  unfold satMem
  simp only [hn, ↓reduceIte]

theorem satMem_arg (i : Nat) (hi : i < 3) :
    satMem.readW (0x8060 + BitVec.ofNat 64 (8 * i)) 64 = satStk.readW (0x8060 + BitVec.ofNat 64 (8 * i)) 64 := by
  refine Mem.readW_congr fun j hj => ?_
  have hn : (0x8060 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x8060 : Addr).toNat < 24 := by
    simp only [Nat.reduceDiv] at hj
    rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    omega
  unfold satMem
  simp only [hn, ↓reduceIte]

/-- A state satisfying the precondition: a 32-byte prime, `e` of one byte,
no `p` and no `rand`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 32 | .r5 => 0x2000 | .r6 => 0x3000 | .r7 => 1 | .r8 => 0x4000
    | .r9 => 0 | .r10 => 0x5000 | _ => 0
  lr := 0
  sp := 0x8000
  mem := satMem
  rd := [⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩, ⟨0x8060, 24⟩, ⟨0x20000, 8192⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 8⟩, ⟨0x10000, 4352⟩]
  syms _ := 0x20000

theorem sat_arg0 : PPC64LE.stackArg satState 0 = 0 :=
  (satMem_arg 0 (by decide)).trans (by decide)
theorem sat_arg1 : PPC64LE.stackArg satState 1 = 0x10000 :=
  (satMem_arg 1 (by decide)).trans (by decide)
theorem sat_arg2 : PPC64LE.stackArg satState 2 = 544 :=
  (satMem_arg 2 (by decide)).trans (by decide)

theorem sat_base : (Spec.RsaKeyGen.candidateContract abi 400).pre (stripConsts TrialTable32.consts satState) := by
  have a2 : PPC64LE.stackArg (stripConsts TrialTable32.consts satState) 2 = 544 := sat_arg2
  unfold Spec.RsaKeyGen.candidateContract
  refine Sig.contract_pre_of_check (by decide +kernel) ?_
  sig_reduce [Spec.RsaKeyGen.candidateSig, abi, argRegs, stackArgs_three, List.append_eq, a2]
  sig_and_intros
  all_goals first
    | trivial
    | decide +kernel

theorem sat_consts : ConstsOk TrialTable32.consts 400 satState := by
  have hl := packed_length
  have held := satMem_held
  rw [consts_eq]
  generalize TrialTable32.packed = W at hl held ⊢
  refine ⟨?_, ?_, ?_⟩
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
    · change r ∈ [⟨0x1000, 32⟩, ⟨0x2000, 8⟩, ⟨0x10000, 4352⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · change r ∈ stackBelow 0x8000 400 at hr
      simp only [stackBelow, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact Region.disjoint_of_sep (by decide)

theorem sat : contract.pre satState := by
  unfold contract Spec.RsaKeyGen.candidateContract
  rw [consts_eq]
  have h₁ := sat_base
  have h₂ := sat_consts
  rw [consts_eq] at h₁ h₂
  exact pre_consts.mpr ⟨h₁, h₂⟩

theorem cand_verified {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) :
    Verified target (VG.Impl.RsaKeyGen.PPC64LE.Candidate.code trial R.name R.code) contract :=
  ⟨cand_correct D R, cand_ct D R, ⟨satState, sat⟩⟩

end VG.Proof.RsaKeyGen.PPC64LE.Cand
