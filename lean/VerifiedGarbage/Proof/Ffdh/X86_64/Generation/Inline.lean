module

public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.AddrArith

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
