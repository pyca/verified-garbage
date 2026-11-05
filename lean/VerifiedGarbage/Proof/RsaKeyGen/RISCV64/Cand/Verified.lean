module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Main
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.CTBase
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract

/-!
# `vg_rsa_keygen_candidate` on RISC-V: the contract

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/Verified.lean`): the contract
with the table of trial division (`abi.withConsts TrialTable32.consts`) and
288 bytes of stack (192 for its frame, 96 for the round's). `pre_facts`: its
precondition gives `CIn` and the table (`TabOk`); `post_of`: `CQ` is its
postcondition; `cand_correct`: the code meets it, with any trial division
that meets `DivOk` and any implementation of the round; `sat`: a state that
satisfies the precondition. `cand_verified_of`: `Verified`, given the
constant time.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64
open VG.Impl.RsaKeyGen (TrialTable32.symbol TrialTable32.packed TrialTable32.consts)
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)

theorem packed_length : TrialTable32.packed.length = 1024 := by
  simp [TrialTable32.packed]

theorem consts_eq : TrialTable32.consts = [(TrialTable32.symbol, TrialTable32.packed)] := rfl

/-- The contract, with the table. -/
abbrev contract : Contract isa := Proof.RsaKeyGen.candidateContract (abi.withConsts TrialTable32.consts) stackBytes

theorem cin_strip {s : State} (h : CIn (stripConsts TrialTable32.consts s)) : CIn s :=
  ⟨h.sp16, h.spLo, h.spHi, List.mem_of_mem_take h.rE, List.mem_of_mem_take h.rP, List.mem_of_mem_take h.rR,
    List.mem_of_mem_take h.rA, h.wr, h.oU, h.oE, h.oP, h.oR, h.oS, h.oA, h.uE, h.uP, h.uR, h.uS, h.uA, h.eS, h.pS,
    h.rS, h.SA, h.Fo, h.Fu, h.Fe, h.Fp, h.Fr, h.FS, h.FA, h.fo, h.fu, h.fe, h.fp, h.fr, h.fS, h.valid, h.el1, h.el2,
    h.plv, h.scr, h.alU, h.alS⟩

theorem tab_of {s : State} (hc : CIn s) (h : ConstsOk TrialTable32.consts stackBytes s) : TabOk s := by
  have hm : (TrialTable32.symbol, TrialTable32.packed) ∈ TrialTable32.consts := by rw [consts_eq]; simp
  have hreg : (⟨s.syms TrialTable32.symbol, 8 * 1024⟩ : Region) ∈ constRegs TrialTable32.consts s := by
    rw [consts_eq, constRegs, Abi.constRegions_cons, Abi.constRegions_nil, packed_length]; simp
  have hw := (h.2.2.1 _ hreg).2.1
  have hr := (h.2.2.1 _ hreg).2.2
  have hal := h.2.2.2 _ hreg
  refine ⟨packed_length ▸ h.fit hm, by simp only at hal; omega, packed_length ▸ h.mem_rd hm,
    fun i hi => h.readW hm (by rw [packed_length]; exact hi), fun ρ hρ => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl
  · exact hw _ (by rw [hc.wr]; simp)
  · exact hw _ (by rw [hc.wr]; simp)
  · exact hw _ (by rw [hc.wr]; simp)
  · exact hr _ (by simp [abi, stackBelow, cF, stackBytes])

theorem pre_facts {s : State} (h : contract.pre s) : CIn s ∧ TabOk s := by
  unfold contract Proof.RsaKeyGen.candidateContract at h
  rw [consts_eq] at h
  obtain ⟨h₁, h₂⟩ := pre_consts.mp h
  have hc := cin_strip (cin_of_pre _ h₁)
  exact ⟨hc, tab_of hc (consts_eq ▸ h₂)⟩

theorem post_of {s s' : State} (hq : CQ s (s'.gpr .a0) s'.mem) : contract.post s s' := by
  unfold contract Proof.RsaKeyGen.candidateContract
  rw [consts_eq]
  refine post_consts.mpr ?_
  sig_post [Proof.RsaKeyGen.candidateSig, abi, argRegs, stackArgs_three, List.append_eq]
  obtain ⟨h1, h2, h3⟩ := hq
  refine ⟨?_, h2, h3⟩
  have hs : Spec.RsaKeyGen.candidateStatus (cOp s) < 4 := by
    unfold Spec.RsaKeyGen.candidateStatus
    split <;> decide
  rw [BitVec.toNat_setWidth, h1, Nat.mod_eq_of_lt (by omega)]
  rfl

theorem cand_correct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) :
    ∀ s, contract.pre s → ∃ t s', Exec isa (VG.Impl.RsaKeyGen.RISCV64.Candidate.code trial R.name R.code) s t s' ∧
      abiPreserved s s' ∧ contract.post s s' := by
  intro s h
  obtain ⟨hc, ht⟩ := pre_facts h
  obtain ⟨t, s', he, ha, hq⟩ := code_correct D R hc ht
  exact ⟨t, s', he, ha, post_of hq⟩

theorem pub_of {s₁ s₂ : State} (hp : contract.pub s₁ s₂) : s₁.sp = s₂.sp ∧ pubOf s₁ = pubOf s₂ := by
  unfold contract Proof.RsaKeyGen.candidateContract at hp
  rw [consts_eq] at hp
  obtain ⟨hp, hsy⟩ := pub_consts.mp hp
  sig_pub [Proof.RsaKeyGen.candidateSig, abi, argRegs, stackArgs_three, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2⟩ := hp
  have hlen : (List.map (fun x => BitVec.toNat x) (eB s₁)).length =
      (List.map (fun x => BitVec.toNat x) (eB s₂)).length := by
    simp only [List.length_map, bytesAt_len, r4]
  obtain ⟨he, hk⟩ := List.append_inj hl hlen
  refine ⟨hsp, ?_⟩
  unfold pubOf
  congr 1
  all_goals first
    | exact hk
    | exact VG.Proof.RsaKeyGen.map_toNat_inj he
    | exact hsy _ (List.mem_singleton_self _)
    | rw [stackArgs_three, stackArgs_three, a0, a1, a2]
    | simp [argRegs, r0, r1, r2, r3, r4, r5, r6, r7]

/-- The stack arguments of the witness: `rand_len` 0, `scratch` at
`0x10000`, `scratch_len` 544, at `0x8000`. -/
def satStk : Mem := fun a => if a = 0x800A then 1 else if a = 0x8010 then 0x20 else if a = 0x8011 then 2 else 0

/-- The witness's memory: its stack arguments, and the table at `0x20000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def satMem : Mem := fun a =>
  if (a - 0x8000).toNat < 24 then satStk a else constMem 0x20000 TrialTable32.packed a

theorem satMem_held : ∀ i < TrialTable32.packed.length,
    satMem.readW (0x20000 + BitVec.ofNat 64 (8 * i)) 64 = TrialTable32.packed.getD i 0 := by
  intro i hi
  rw [← constMem_held _ _ (by rw [packed_length]; decide) i hi]
  refine Mem.readW_congr fun j hj => ?_
  have hn : ¬ (0x20000 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x8000 : Addr).toNat < 24 := by
    rw [packed_length] at hi
    simp only [Nat.reduceDiv] at hj
    have h1 : (0x20000 : Addr).toNat = 131072 := rfl
    have h2 : (0x8000 : Addr).toNat = 32768 := rfl
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h1, h2]
    omega
  unfold satMem
  simp only [hn, ↓reduceIte]

theorem satMem_arg (i : Nat) (hi : i < 3) :
    satMem.readW (0x8000 + BitVec.ofNat 64 (8 * i)) 64 = satStk.readW (0x8000 + BitVec.ofNat 64 (8 * i)) 64 := by
  refine Mem.readW_congr fun j hj => ?_
  have hn : (0x8000 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x8000 : Addr).toNat < 24 := by
    simp only [Nat.reduceDiv] at hj
    rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    omega
  unfold satMem
  simp only [hn, ↓reduceIte]

/-- A state satisfying the precondition: a 32-byte prime, `e` of one byte,
no `p` and no `rand`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 32 | .a2 => 0x2000 | .a3 => 0x3000 | .a4 => 1 | .a5 => 0x4000
    | .a6 => 0 | .a7 => 0x5000 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := [⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩, ⟨0x8000, 24⟩, ⟨0x20000, 8192⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 8⟩, ⟨0x10000, 4352⟩]
  syms _ := 0x20000

theorem sat_arg0 : stackArg satState 0 = 0 :=
  (satMem_arg 0 (by decide)).trans (by decide)
theorem sat_arg1 : stackArg satState 1 = 0x10000 :=
  (satMem_arg 1 (by decide)).trans (by decide)
theorem sat_arg2 : stackArg satState 2 = 544 :=
  (satMem_arg 2 (by decide)).trans (by decide)

theorem sat_base : (Proof.RsaKeyGen.candidateContract abi stackBytes).pre (stripConsts TrialTable32.consts satState) := by
  have a0 : stackArg (stripConsts TrialTable32.consts satState) 0 = 0 := sat_arg0
  have a1 : stackArg (stripConsts TrialTable32.consts satState) 1 = 0x10000 := sat_arg1
  have a2 : stackArg (stripConsts TrialTable32.consts satState) 2 = 544 := sat_arg2
  have e : stackBytes = 287 + 1 := rfl
  rw [e]
  unfold Proof.RsaKeyGen.candidateContract
  refine Sig.contract_pre_of_check (by decide +kernel) ?_
  sig_reduce [Proof.RsaKeyGen.candidateSig, abi, argRegs, stackArgs_three, List.append_eq, a0, a1, a2]
  sig_and_intros
  all_goals first
    | trivial
    | decide +kernel

theorem sat_consts : ConstsOk TrialTable32.consts stackBytes satState := by
  have hl := packed_length
  have held := satMem_held
  rw [consts_eq]
  generalize TrialTable32.packed = W at hl held ⊢
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
    · change r ∈ [⟨0x1000, 32⟩, ⟨0x2000, 8⟩, ⟨0x10000, 4352⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · change r ∈ stackBelow 0x8000 stackBytes at hr
      simp only [stackBelow, stackBytes, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact Region.disjoint_of_sep (by decide)
  · rw [constRegs, Abi.constRegions_cons, Abi.constRegions_nil, hl]
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    decide

theorem sat : contract.pre satState := by
  unfold contract Proof.RsaKeyGen.candidateContract
  rw [consts_eq]
  have h₁ := sat_base
  have h₂ := sat_consts
  rw [consts_eq] at h₁ h₂
  exact pre_consts.mpr ⟨h₁, h₂⟩

end VG.Proof.RsaKeyGen.RISCV64.Cand
