module

-- separate module: the candidate's verification builds in parallel with the controller's correctness and constant time

public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.CT
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCall
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCallCT
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.RISCV64.Search

/-!
# An FFDH parameter candidate on RISC-V, verified for any round

`roundCall_spec`: the round's call (`Search.roundCall_ok`,
`Search.roundCall_ct`) meets `RoundCall`, so `candidate_correct` and
`candidate_ct` hold for any implementation of the round, against the
internal contract `Proof.Ffdh.sievedParameterCandidateContract` under
`abi.withConsts` with RSA's table of trial division (`pc_pre`, `pc_post`,
`pc_pub`), with the 96 bytes of stack below `sp` its frame uses
(`candidate_stack`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

open VG VG.RISCV64
open VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Impl.MillerRabin.RISCV64.Search (roundCall)
open VG.Impl.Ffdh.RISCV64.Search (millerRabin draw round)
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)

theorem prep_to {s : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) :
    VG.Proof.MillerRabin.RISCV64.Search.Prep s B L w c :=
  ⟨h.env, h.len, h.wW, h.strideW, h.arrW, h.ctx.n, h.c3, h.odd, h.inv, h.ctx.inv, h.r1, h.r9, h.r10, h.e, h.l⟩

theorem prep_of {s : State} {B : Addr} {L w c : Nat} (h : VG.Proof.MillerRabin.RISCV64.Search.Prep s B L w c) :
    Prep s B L w c :=
  ⟨⟨h.env.hs, h.env.hw, h.env.hw', h.env.hZ, h.env.a7, h.env.s5, h.env.t0, h.t1, h.n⟩, h.env.s6, h.len, h.wW,
    h.strideW, h.arrW, h.c3, h.odd, h.inv, h.r1, h.r9, h.r10, h.e, h.l⟩

/-- The round's call, as `Search.RoundCall` and `Search.RoundCallCT` prove it. -/
theorem roundCall_spec (R : RoundImpl) : RoundCall R where
  ok := fun _ _ ⟨hp, ha, hac, hsp, h16, hd⟩ =>
    WP.mono (VG.Proof.MillerRabin.RISCV64.Search.roundCall_ok R (prep_to hp) ha hac h16 hsp hd) fun _ ht =>
      ⟨prep_of ht.prep, ht.a0, ht.keeps, ht.frame, ht.rd, ht.wr, ht.sp⟩
  ct := (VG.Proof.Ffdh.RISCV64.Search.roundCall_ct R).mono
    (fun _ _ ⟨d, ⟨p₁, a₁, c₁, sp₁, s₁, d₁⟩, ⟨p₂, a₂, c₂, sp₂, s₂, d₂⟩, hsp⟩ =>
      ⟨⟨d.B, d.L, d.w, d.c, d.a⟩, ⟨prep_to p₁, a₁, c₁, s₁, sp₁, d₁⟩, ⟨prep_to p₂, a₂, c₂, s₂, sp₂, d₂⟩, hsp⟩)
    fun _ _ h => h

/-- The candidate calling the round `v`. -/
abbrev candCode (v : RoundImpl) : Prog isa := code v.name v.code

theorem sdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : sdepth c = 0 := by
  induction c <;> simp_all [Code.noFrames, sdepth]

/-- The candidate uses the stack its round does. -/
theorem candidate_stack (v : RoundImpl) : sdepth (candCode v) ≤ 96 := by
  simp only [candCode, code, main, tests, testQ, testRest, test, millerRabin, draw, round, roundCall, pResult,
    qResult, ite_true,
    ite_false, Bool.false_eq_true, sdepth]
  simp (disch := decide) only [sdepth_of_noFrames, Nat.max_zero, Nat.zero_max, Nat.max_self]
  exact v.stack

/-! ## The internal contract, under `abi.withConsts` -/

/-- RSA's table of trial division. -/
abbrev tables : List (String × List (BitVec 64)) := VG.Impl.RsaKeyGen.TrialTable32.consts

/-- The candidate's internal contract, as its caller states it. -/
abbrev candContract : Contract isa := Proof.Ffdh.sievedParameterCandidateContract (abi.withConsts tables) 96

/-- `pcPre` without the table. -/
def pcBase (s : State) : Prop :=
  let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
  let used : Region := ⟨s.gpr .a2, 8⟩
  let rand : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
  let scr : Region := ⟨s.gpr .a7, (stackArg s 0).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 8⟩
  let below : Region := ⟨s.sp - BitVec.ofNat 64 96, 96⟩
  96 ≤ s.sp.toNat ∧ s.sp.toNat % 16 = 0 ∧ s.sp.toNat + 8 ≤ 2 ^ 64 ∧
    s.rd = [rand, args] ∧ s.wr = [out, used, scr] ∧
    out.Disjoint used ∧ out.Disjoint rand ∧ out.Disjoint scr ∧ out.Disjoint args ∧
    used.Disjoint rand ∧ used.Disjoint scr ∧ used.Disjoint args ∧
    rand.Disjoint scr ∧ scr.Disjoint args ∧
    below.Disjoint out ∧ below.Disjoint used ∧ below.Disjoint rand ∧ below.Disjoint scr ∧ below.Disjoint args ∧
    (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat % 8 = 0 ∧ (s.gpr .a7).toNat % 8 = 0 ∧
    512 ≤ (s.gpr .a3).toNat ∧ (s.gpr .a3).toNat ≤ 8192 ∧
    (s.gpr .a1).toNat = ((s.gpr .a3).toNat + 7) / 8 ∧
    (((s.gpr .a4).setWidth 32).toNat = 2 ∨ ((s.gpr .a4).setWidth 32).toNat = 5) ∧
    Spec.Rsa.scratchWords (s.gpr .a1).toNat ≤ (stackArg s 0).toNat

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem pc_base (s : State) (h : (Proof.Ffdh.sievedParameterCandidateContract abi 96).pre s) : pcBase s := by
  sig_pre [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs,
    stackBelow, pcBase, stackArgs_one, List.append_eq] at h
  sig_pre [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs,
    stackBelow, pcBase, stackArgs_one, List.append_eq] at h
  sig_split h
  sig_reduce [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs,
    stackBelow, pcBase, stackArgs_one, List.append_eq]
  sig_and_intros
  sig_close
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | omega

private theorem tables_eq' :
    tables = [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] := rfl

private theorem packed_length' : VG.Impl.RsaKeyGen.TrialTable32.packed.length = 1024 :=
  Proof.RsaKeyGen.TrialTable32.packed_length

theorem pc_pre (s : State) (h : candContract.pre s) : pcPre s := by
  unfold candContract Proof.Ffdh.sievedParameterCandidateContract at h
  rw [tables_eq'] at h
  obtain ⟨h₁, hc⟩ := pre_consts.mp h
  obtain ⟨a1, a2, a3, hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, q1, q2, q3, q4, q5, n1, n2, n3, n4, al1, al2,
    b1, b2, hL, hg, hsw⟩ := pc_base _ h₁
  have hrd' : (stripConsts _ s).rd = [⟨s.gpr .a5, (s.gpr .a6).toNat⟩, ⟨stackArgAddr s 0, 8⟩] := hrd
  have hwr' : s.wr = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩, ⟨s.gpr .a2, 8⟩, ⟨s.gpr .a7, (stackArg s 0).toNat * 8⟩] := hwr
  have hreg : constRegs [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] s =
      [tabR s] := by
    rw [constRegs, Abi.constRegions_cons, Abi.constRegions_nil, packed_length']
  have hrd₂ : s.rd = [⟨s.gpr .a5, (s.gpr .a6).toNat⟩, ⟨stackArgAddr s 0, 8⟩, tabR s] := by
    rw [← List.take_append_drop (s.rd.length -
      [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)].length) s.rd, hc.1, hreg]
    change (stripConsts _ s).rd ++ _ = _
    rw [hrd']; rfl
  have hm := List.mem_singleton_self (VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)
  have hfit := hc.fit hm
  have hal := hc.aligned hm
  rw [packed_length'] at hfit
  have hw := hc.wr1
  rw [packed_length'] at hw
  refine ⟨a1, a2, a3, hrd₂, hwr', d1, d2, d3, d4, d5, d6, d7, d8, d9, q1, q2, q3, q4, q5, n1, n2, n3, n4, al1,
    al2, b1, b2, hL, hg, hsw, hfit, by omega, fun i hi => ?_, hw _ (by rw [hwr']; simp),
    hw _ (by rw [hwr']; simp)⟩
  have e := hc.readW hm (by rw [packed_length']; exact hi)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [packed_length']; exact hi), Option.getD_some,
    Proof.RsaKeyGen.TrialTable32.packed_entry hi] at e
  exact e

theorem pc_post₀ : ∀ s t, True → pcPost s t → (Proof.Ffdh.sievedParameterCandidateContract abi 96).post s t := by
  sig_implies_post [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs,
    pcPost, pcResult, pcRand, stackArgs_one, List.append_eq]

theorem pc_post (s t : State) (h : pcPost s t) : candContract.post s t := by
  unfold candContract Proof.Ffdh.sievedParameterCandidateContract
  rw [tables_eq']
  exact post_consts.mpr (pc_post₀ s t trivial h)

theorem pc_pub (s t : State) (h : candContract.pub s t) : pcPub s t := by
  unfold candContract Proof.Ffdh.sievedParameterCandidateContract at h
  rw [tables_eq'] at h
  obtain ⟨hp, hsy⟩ := pub_consts.mp h
  sig_pub [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs,
    stackArgs_one, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l⟩ := hp
  exact ⟨a, b, c, d, e, f, g, i, j, k, l, hsy _ (List.mem_singleton_self _)⟩

/-- `vg_ffdh_parameter_candidate_sieved` meets its internal contract, for any
implementation of the round. -/
theorem candidate_correct (v : RoundImpl) (s : State) (h : candContract.pre s) :
    ∃ t s', Exec isa (candCode v) s t s' ∧ abiPreserved s s' ∧ candContract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := code_correct (roundCall_spec v) s (pc_pre s h)
  exact ⟨t, s', he, ha, pc_post s s' hp⟩

/-- And in constant time. -/
theorem candidate_ct (v : RoundImpl) : ConstantTime isa candContract.pre candContract.pub (candCode v) :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
    code_ct (roundCall_spec v) s₁ s₂ t₁ t₂ s₁' s₂' (pc_pre _ h₁) (pc_pre _ h₂) (pc_pub _ _ hp) e₁ e₂

end VG.Proof.Ffdh.RISCV64.ParameterCandidate
