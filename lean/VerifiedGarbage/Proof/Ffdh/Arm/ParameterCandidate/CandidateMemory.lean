module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Candidate control flow preserves all arguments except its explicit entropy count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

private theorem values_other (p : CandidateParams) (consumed next d : Nat) (different : d ≠ 40) :
    candidateValues p consumed d = candidateValues p next d := by
  unfold candidateValues
  split <;> simp_all

private theorem CandidateContext.saved_separate {s : State} {p : CandidateParams} {consumed d : Nat}
    (h : CandidateContext p consumed s) (fit : d + 4 ≤ 40) :
    ∀ r ∈ candidateRegions p s.sp, (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [candidateRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
    exact h.stackOutput.sub_left (Offset.sub_base _ (by omega))
  · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
    exact h.stackScratch.sub_left (Offset.sub_base _ (by omega))
  · change (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint
      ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩
    rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega), FrameStack.addr_sub' h.stackBelow]
    exact Offset.disjoint_below _ (by omega)
  · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega), VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
    exact Offset.disjoint _ (.inl fit) (by omega) (by decide)

theorem CandidateContext.after_frame {s t : State} {p : CandidateParams} {consumed next : Nat} {rs : List Reg}
    (h : CandidateContext p consumed s) (bound : next ≤ p.bytes.length)
    (usedWord : t.mem.readW (State.addr (t.sp + 40#32)) 32 = BitVec.ofNat 32 next)
    (changed : Frame (candidateRegions p s.sp) s.mem t.mem) (rest : Rest rs s t) :
    CandidateContext p next t := by
  have saved : SavedFrame (candidateValues p next) candidateSlots t := by
    refine ⟨?_, ?_⟩
    · rw [rest.sp]; exact h.saved.space.congr rest.wr
    · intro d hd
      by_cases count : d = 40
      · subst d
        change t.mem.readW (State.addr (t.sp + 40#32)) 32 = BitVec.ofNat 32 next
        exact usedWord
      · have fit : d + 4 ≤ 40 := by
          simp only [candidateSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
          omega
        rw [rest.sp, changed.readW (a := State.addr (s.sp + BitVec.ofNat 32 d)) (w := 32)
          (r := ⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩) (Region.contains_self _ _)
          (h.saved_separate fit) (by decide)]
        exact (h.saved.saved d hd).trans (values_other p consumed next d count)
  refine ⟨saved, h.workspace.congr rest.wr, ?_, ?_, ?_, ?_, bound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rest.wr]; exact h.outputWrite
  · rw [rest.wr]; exact h.usedWrite
  · rw [rest.rd, rest.wr]; exact h.tapeRead
  · refine (rsa_bytes_frame changed (by have := p.tapeCount; omega) ?_).trans h.tapeBytes
    intro r hr
    simp only [candidateRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact p.outputTape.symm
    · exact p.tapeScratch
    · exact h.belowTape.symm
    · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
      exact h.stackTape.symm.sub_right (Offset.sub_base _ (by decide : 40 + 28 ≤ 72))
  · rw [rest.sp]; exact h.stackBelow
  · rw [rest.sp]; exact h.stackOutput
  · rw [rest.sp]; exact h.stackUsed
  · rw [rest.sp]; exact h.stackScratch
  · rw [rest.sp]; exact h.stackTape
  · rw [rest.sp]; exact h.belowOutput
  · rw [rest.sp]; exact h.belowUsed
  · rw [rest.sp]; exact h.belowScratch
  · rw [rest.sp]; exact h.belowTape

theorem CandidateContext.after_memory {s t : State} {p : CandidateParams} {consumed : Nat} {rs : List Reg}
    (h : CandidateContext p consumed s) (memory : t.mem = s.mem) (rest : Rest rs s t) :
    CandidateContext p consumed t := by
  refine h.after_frame h.consumedBound ?_ (by rw [memory]; exact Frame.refl _ _) rest
  rw [memory, rest.sp]
  simpa only [candidateValues] using h.saved.saved 40 (by simp [candidateSlots])

end VG.Proof.Ffdh.Arm.ParameterCandidate
