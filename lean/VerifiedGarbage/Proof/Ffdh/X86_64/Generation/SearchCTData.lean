module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.Inline
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCallPre
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCandidatePost


/-! # Public positions in a native search; saved caller registers stay private -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64

structure SearchPoint where
  inputs : SearchPublic
  used : Nat
  remaining : Nat

def SearchCTL (p : SearchPoint) (s : State) : Prop :=
  ∃ original, SearchLive p.inputs original p.used p.remaining s

def SearchAllocated (p : SearchPoint) (s : State) : Prop :=
  ∃ original before, SearchLive p.inputs original p.used p.remaining before ∧ s = allocated 32 before

def SearchCallCT (p : SearchPoint) (s : State) : Prop :=
  InlinePre VG.Proof.Ffdh.X86_64.ParameterCandidate.pcContract
    (fun _ => callReads p.inputs p.used) (fun _ => callWrites p.inputs) s ∧
  SearchArgs p.inputs p.used s ∧ s.gpr .rsp = p.inputs.c.sp - 32 ∧
  VG.Proof.Ffdh.X86_64.ParameterCandidate.pcRand s = p.inputs.c.rand.drop p.used ∧
  stackArg s 0 = BitVec.ofNat 64 (p.inputs.c.rand.length - p.used) ∧
  stackArg s 1 = p.inputs.c.B ∧ stackArg s 2 = BitVec.ofNat 64 (p.inputs.c.Z / 8)

def SearchCandidateCT (p : SearchPoint) (s : State) : Prop :=
  ∃ original, SearchLive p.inputs original p.used p.remaining s ∧ SearchCandidatePost p.inputs p.used s

theorem search_ctl_pins : Pins SearchCTL [.r12, .rsp] := by
  intro p s t ⟨o₁, h₁⟩ ⟨o₂, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [h₁.r12.trans h₂.r12.symm, h₁.rsp.trans h₂.rsp.symm]

theorem search_allocated_pins : Pins SearchAllocated [.r12, .rsp] := by
  rintro p s t ⟨_, a, h₁, rfl⟩ ⟨_, b, h₂, rfl⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h₁.r12.trans h₂.r12.symm
  · rw [allocated_rsp, allocated_rsp, h₁.rsp, h₂.rsp]

end VG.Proof.Ffdh.X86_64.Generation
