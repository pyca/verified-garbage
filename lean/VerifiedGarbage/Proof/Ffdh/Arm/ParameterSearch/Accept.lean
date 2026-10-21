module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.AcceptHead
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CandidateFacts
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Result
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.PolicyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.FieldMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Memory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Done
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset

/-! Acceptance records the exact consumption and prime, clearing all persistent retry policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord lowWord_store)

theorem SearchLive.accept {p : SearchParams} {used remaining prime : Nat} {s : State}
    {rand : Spec.RsaKeyGen.Rand} (h : SearchLive p used remaining s) (post : CandidatePost p used s)
    (candidate : candidateResult p used = some (some prime, rand)) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.accept) s fun t =>
      SearchDone p (.accepted prime (used + candidateUsed p used)) t ∧ Rest [.r9, .r10, .r11] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.accept
  rw [WP.block_append_iff]
  refine WP.mono (acceptHead_ok h post.consumed_low) ?_
  rintro u ⟨memU, restU⟩
  have controlU : Controller p.control u :=
    ⟨h.buffers.controller.space.congr restU.wr, (restU.gpr .r4 (by simp)).trans h.buffers.controller.ptr⟩
  refine WP.mono (terminal_ok u controlU (Or.inl rfl)) ?_
  rintro t ⟨memT, restT⟩
  have rest : Rest [.r9, .r10, .r11] s t :=
    (restU.mono (by simp)).trans (restT.mono (by simp))
  have first : Frame [⟨State.addr p.control, 128⟩] s.mem u.mem := by
    rw [memU]
    exact (Frame.refl _ _).writeW (by simp) _ (Offset.contains_base _ (by decide : 32 + 4 ≤ 128) (by decide))
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
    apply first.trans
    rw [memT]
    exact terminalMem_frame _ _ _
  have oldOutput : searchOutput p (.accepted prime (used + candidateUsed p used)) s.mem := by
    simpa only [searchOutput, candidate] using post.output
  refine ⟨⟨h.buffers.after_frame (by decide) (frame.mono (by simp [searchRegions])) rest,
    by change used + candidateUsed p used ≤ p.c.bytes.length; have := candidateUsed_bound p used; have := h.usedBound; omega, ?_, ?_, ?_, ?_,
    control_output oldOutput frame⟩, rest⟩
  · rw [memT, terminalMem_low _ _ _ 6 (by decide)]
    simp only [show ¬(6 = 13) by decide, show ¬(6 = 0 ∨ 6 = 3) by decide, ite_false]
    rw [memU, lowWord_store (i := 4) _ _ _ (by decide) (by decide)]
    exact h.saved 6 (by simp [searchSlots])
  · rw [memT, terminalMem_low _ _ _ 4 (by decide)]
    simp only [show ¬(4 = 13) by decide, show ¬(4 = 0 ∨ 4 = 3) by decide, ite_false]
    rw [memU, lowWord_store (i := 4) _ _ _ (by decide) (by decide)]
    rfl
  · rw [memT, terminalMem_low _ _ _ 13 (by decide)]
    rfl
  · have width : u.mem.readW (off (State.addr p.control) 8) 64 = BitVec.ofNat 64 p.c.length := by
      rw [memU]
      exact (fields_word s.mem p.control [(4, BitVec.ofNat 32 (used + candidateUsed p used))]
        (by simp) (j := 1) (by decide) (by simp)).trans h.width
    have entropy : u.mem.readW (off (State.addr p.control) 16) 64 =
        BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits) := by
      rw [memU]
      exact (fields_word s.mem p.control [(4, BitVec.ofNat 32 (used + candidateUsed p used))]
        (by simp) (j := 2) (by decide) (by simp)).trans h.entropy
    change [t.mem.readW (off (State.addr p.control) 0) 64,
      t.mem.readW (off (State.addr p.control) 8) 64,
      t.mem.readW (off (State.addr p.control) 16) 64,
      t.mem.readW (off (State.addr p.control) 24) 64] = _
    rw [memT, terminalMem_word _ _ _ 0 (by decide), terminalMem_word _ _ _ 1 (by decide),
      terminalMem_word _ _ _ 2 (by decide), terminalMem_word _ _ _ 3 (by decide), width, entropy]
    rfl

end VG.Proof.Ffdh.Arm.ParameterSearch
