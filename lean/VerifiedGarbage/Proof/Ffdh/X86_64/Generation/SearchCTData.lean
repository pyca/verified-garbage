module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCallPre
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCandidatePost
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ffdh.X86_64.Generation.Inline`, which this module and modules that import it used -/

section

/-! # Reuse a verified generation operation inside a controller

Unlike `WP.inline`, the operation may contain calls. Its stack footprint is
retained in the frame, so the controller's persistent state must be disjoint
from that footprint as well as the operation's writable buffers.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64

theorem inline_stack {c : Prog isa} {k : Contract isa} {stack : Nat}
    (correct : ∀ s, k.pre s → ∃ tr t, Exec isa c s tr t ∧ abiPreserved s t ∧ k.post s t)
    (safe : SpSafe c) (depth : c.x86_64Depth ≤ stack) (small : stack < 2 ^ 64)
    {s : State} {rd wr : List Region} (pre : k.pre (s.withRegions rd wr))
    (reads : Covers (rd ++ wr) (s.rd ++ s.wr)) (writes : Covers wr s.wr) :
    WP isa c s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ abiPreserved s t ∧
      Frame (wr ++ [below (s.gpr .rsp) stack]) s.mem t.mem ∧
      k.post (s.withRegions rd wr) (t.withRegions rd wr) := by
  obtain ⟨tr, u, he, ha, hp⟩ := correct _ pre
  have hf := Exec.stackFrame safe he (Nat.lt_of_le_of_lt depth small)
  simp only [State.withRegions_gpr, State.withRegions_mem, State.withRegions_wr] at hf
  have hf' : Frame (wr ++ [below (s.gpr .rsp) stack]) s.mem u.mem :=
    hf.sub fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst r
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          Offset.below_mono _ depth small⟩
  have hw := Exec.widen he reads writes
  simp only [State.withRegions_withRegions, State.withRegions_self] at hw
  refine ⟨tr, u.withRegions s.rd s.wr, hw, rfl, rfl, ?_, hf', ?_⟩
  · exact ha
  · obtain ⟨hr, hw⟩ := Exec.rdwr he
    simp only [State.withRegions_rd, State.withRegions_wr] at hr hw
    have hu : u.withRegions rd wr = u := by
      rw [← hr, ← hw, State.withRegions_self]
    simpa only [State.withRegions_withRegions, hu] using hp

def InlinePre (k : Contract isa) (rd wr : State → List Region) (s : State) : Prop :=
  k.pre (s.withRegions (rd s) (wr s)) ∧
    Covers (rd s ++ wr s) (s.rd ++ s.wr) ∧ Covers (wr s) s.wr

theorem inline_constantTime {c : Prog isa} {k : Contract isa}
    (correct : ∀ s, k.pre s → ∃ tr t, Exec isa c s tr t)
    (ct : ConstantTime isa k.pre k.pub c) (rd wr : State → List Region) :
    ConstantTime isa (InlinePre k rd wr)
      (fun s t => k.pub (s.withRegions (rd s) (wr s)) (t.withRegions (rd t) (wr t))) c := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ h₁ h₂ hp he₁ he₂
  obtain ⟨trn₁, u₁, hn₁⟩ := correct _ h₁.1
  obtain ⟨trn₂, u₂, hn₂⟩ := correct _ h₂.1
  have hw₁ := Exec.widen hn₁ h₁.2.1 h₁.2.2
  have hw₂ := Exec.widen hn₂ h₂.2.1 h₂.2.2
  simp only [State.withRegions_withRegions, State.withRegions_self] at hw₁ hw₂
  rw [(Exec.det he₁ hw₁).1, (Exec.det he₂ hw₂).1]
  exact ct _ _ _ _ _ _ h₁.1 h₂.1 hp hn₁ hn₂

end VG.Proof.Ffdh.X86_64.Generation

end

end

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
