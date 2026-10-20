module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Lift exact output, scratch and local-word effects into candidate state. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

private theorem CandidateContext.after_separate {s t : State} {p : CandidateParams} {consumed : Nat}
    {regions : List Region} {rs : List Reg} (h : CandidateContext p consumed s)
    (changed : Frame regions s.mem t.mem)
    (within : ∀ r ∈ regions, ∃ r' ∈ candidateRegions p s.sp, r.Sub r')
    (separate : ∀ r ∈ regions, (⟨State.addr (s.sp + 40#32), 4⟩ : Region).Disjoint r)
    (rest : Rest rs s t) : CandidateContext p consumed t := by
  refine h.after_frame h.consumedBound ?_ (changed.sub within) rest
  rw [rest.sp, changed.readW (r := ⟨State.addr (s.sp + 40#32), 4⟩) (Region.contains_self _ _) separate (by decide)]
  simpa only [candidateValues] using h.saved.saved 40 (by simp [candidateSlots])

theorem CandidateContext.after_output {s t : State} {p : CandidateParams} {consumed : Nat} {rs : List Reg}
    (h : CandidateContext p consumed s) (changed : Frame [⟨State.addr p.out, p.length⟩] s.mem t.mem)
    (rest : Rest rs s t) : CandidateContext p consumed t := by
  refine h.after_separate changed ?_ ?_ rest
  · intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨_, by simp [candidateRegions], fun _ h => h⟩
  · intro r hr
    rw [List.mem_singleton] at hr
    subst r
    rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
    exact h.stackOutput.sub_left (Offset.sub_base _ (by decide : 40 + 4 ≤ 72))

theorem CandidateContext.after_workspace {s t : State} {p : CandidateParams} {consumed : Nat} {rs : List Reg}
    (h : CandidateContext p consumed s) (changed : Frame [⟨State.addr p.base, 8 * p.capacity⟩] s.mem t.mem)
    (rest : Rest rs s t) : CandidateContext p consumed t := by
  refine h.after_separate changed ?_ ?_ rest
  · intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨_, by simp [candidateRegions], fun _ h => h⟩
  · intro r hr
    rw [List.mem_singleton] at hr
    subst r
    rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
    exact h.stackScratch.sub_left (Offset.sub_base _ (by decide : 40 + 4 ≤ 72))

theorem CandidateContext.after_aux {s t : State} {p : CandidateParams} {consumed d : Nat} {rs : List Reg}
    (h : CandidateContext p consumed s) (lower : 44 ≤ d) (upper : d + 4 ≤ 68)
    (changed : Frame [⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩] s.mem t.mem) (rest : Rest rs s t) :
    CandidateContext p consumed t := by
  refine h.after_separate changed ?_ ?_ rest
  · intro r hr
    rw [List.mem_singleton] at hr
    subst r
    refine ⟨⟨State.addr (s.sp + 40#32), 28⟩, by simp [candidateRegions], ?_⟩
    rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega), VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
    exact Offset.sub _ (by omega) (by omega)
  · intro r hr
    rw [List.mem_singleton] at hr
    subst r
    rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega), VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
    exact Offset.disjoint _ (.inl lower) (by decide) (by omega)

theorem CandidateContext.store_consumed {s t : State} {p : CandidateParams} {consumed next : Nat} {rs : List Reg}
    (h : CandidateContext p consumed s) (bound : next ≤ p.bytes.length)
    (memory : t.mem = s.mem.writeW (State.addr (s.sp + 40#32)) (BitVec.ofNat 32 next))
    (rest : Rest rs s t) : CandidateContext p next t := by
  refine h.after_frame bound ?_ ?_ rest
  · rw [rest.sp, memory, Mem.readW_writeW_self32]
  · rw [memory]
    have changed : Frame [⟨State.addr (s.sp + 40#32), 4⟩] s.mem
        (s.mem.writeW (State.addr (s.sp + 40#32)) (BitVec.ofNat 32 next)) :=
      (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
    refine changed.sub ?_
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨⟨State.addr (s.sp + 40#32), 28⟩, by simp [candidateRegions], Region.sub_prefix (by decide : 4 ≤ 28)⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
