module

-- separate module: the candidate's verification builds in parallel with the controller's correctness and constant time

public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.CT
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCall
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCallCT
public import VerifiedGarbage.Proof.Ffdh.Contract

/-!
# An FFDH parameter candidate on RISC-V, verified for any round

`roundCall_spec`: the round's call (`Search.roundCall_ok`,
`Search.roundCall_ct`) meets `RoundCall`, so `candidate_verified` holds for
any implementation of the round, with the 96 bytes of stack below `sp` its
frame uses (`candidate_stack`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

open VG VG.RISCV64
open VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Impl.MillerRabin.RISCV64.Search (millerRabin draw round roundCall)
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
  ct := (VG.Proof.MillerRabin.RISCV64.Search.roundCall_ct R).mono
    (fun _ _ ⟨d, ⟨p₁, a₁, c₁, sp₁, s₁, d₁⟩, ⟨p₂, a₂, c₂, sp₂, s₂, d₂⟩, hsp⟩ =>
      ⟨⟨d.B, d.L, d.w, d.c, d.a⟩, ⟨prep_to p₁, a₁, c₁, s₁, sp₁, d₁⟩, ⟨prep_to p₂, a₂, c₂, s₂, sp₂, d₂⟩, hsp⟩)
    fun _ _ h => h

/-- The candidate calling the round `v`. -/
abbrev candCode (v : RoundImpl) : Prog isa := code v.name v.code

theorem sdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : sdepth c = 0 := by
  induction c <;> simp_all [Code.noFrames, sdepth]

/-- The candidate uses the stack its round does. -/
theorem candidate_stack (v : RoundImpl) : sdepth (candCode v) ≤ 96 := by
  simp only [candCode, code, main, tests, test, millerRabin, draw, round, roundCall, pResult, qResult, ite_true,
    ite_false, Bool.false_eq_true, sdepth]
  simp (disch := decide) only [sdepth_of_noFrames, Nat.max_zero, Nat.zero_max, Nat.max_self]
  exact v.stack

/-- `vg_ffdh_parameter_candidate` meets its contract, for any implementation
of the round. -/
theorem candidate_verified (v : RoundImpl) :
    Verified RISCV64.target (candCode v) (Proof.Ffdh.parameterCandidateContract RISCV64.abi 96) :=
  Verified.of_correct (code_correct (roundCall_spec v)) (code_ct (roundCall_spec v)) pc_implies

end VG.Proof.Ffdh.RISCV64.ParameterCandidate
