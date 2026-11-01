module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Call
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.LiveGuards
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Exit
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Result
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CandidateFacts
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.PolicyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.FieldMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Memory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Done
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Advance
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CompareResult
public import VerifiedGarbage.Proof.Ffdh.Contract
/-! One native search step calls a candidate only when the entropy suffix can hold its modulus. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/AcceptHead.lean`, which only this module imported.
section

/-! Accepting a candidate records exactly its consumed entropy before clearing the policy. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

theorem acceptHead_ok {p : SearchParams} {used remaining count : Nat} {s : State}
    (h : SearchLive p used remaining s)
    (consumed : lowWord s.mem p.control 14 = BitVec.ofNat 32 count) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.acceptHead) s fun t =>
      t.mem = s.mem.writeW (off (State.addr p.control) 32) (BitVec.ofNat 32 (used + count)) ∧
        Rest [.r9, .r10] s t := by
  have usedValue := h.saved 4 (by simp [searchSlots])
  simp only [searchValues] at usedValue
  refine withRest_all [.r9, .r10] ?_ (by rfl) (by rfl)
  have control := h.buffers.controller
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.acceptHead VG.Impl.Ffdh.Arm.ParameterSearch.ldf
    VG.Impl.Ffdh.Arm.ParameterSearch.stf lowWord at *
  ffrun [control.addr (by decide : 14 < 16), control.addr (by decide : 4 < 16),
    control.read (by decide : 14 < 16), control.read (by decide : 4 < 16),
    control.write (by decide : 4 < 16), consumed, usedValue, BitVec.ofNat_add_ofNat]

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/Accept.lean`, which only this module imported.
section

/-! Acceptance records the exact consumption and prime, clearing all persistent retry policy. -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/Status.lean`, which only this module imported.
section

/-! The internal continue status preserves every externally persistent live search field. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord writeLow lowWord_store)

theorem againBlock_ok (s : State) {base : BitVec 32} (h : Controller base s) :
    WP isa (.block [.mov .r11 (.imm 4), VG.Impl.Ffdh.Arm.ParameterSearch.stf .r11 13]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) 104) (4#32) ∧ Rest [.r11] s t := by
  refine withRest_all [.r11] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.stf
  ffrun [h.addr (by decide : 13 < 16), h.write (by decide : 13 < 16)]
  rfl

theorem status_word (m : Mem) (base : BitVec 32) (value : BitVec 32) {j : Nat}
    (hj : j < 13) :
    (m.writeW (off (State.addr base) 104) value).readW (off (State.addr base) (8 * j)) 64 =
      m.readW (off (State.addr base) (8 * j)) 64 := by
  have word := fields_word m base [(13, value)] (by simp) (j := j) (by omega) (by simp; omega)
  exact word

theorem SearchLive.again {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) :
    WP isa (.block [.mov .r11 (.imm 4), VG.Impl.Ffdh.Arm.ParameterSearch.stf .r11 13]) s fun t =>
      (SearchLive p used remaining t ∧ lowWord t.mem p.control 13 = 4#32) ∧ Rest [.r11] s t := by
  refine WP.mono (againBlock_ok s h.buffers.controller) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ (Offset.contains_base _ (by decide : 104 + 4 ≤ 128) (by decide))
  refine ⟨⟨?_, ?_⟩, rest⟩
  · refine SearchLive.after_control (nextUsed := used) (nextRemaining := remaining)
      h (by decide) frame rest h.usedBound h.remainingBound ?_ ?_ ?_ ?_
    · have word := status_word s.mem p.control 4#32 (j := 0) (by decide)
      have address : off (State.addr p.control) 0 = State.addr p.control := by simp [off]
      rw [show 8 * 0 = 0 from rfl, address] at word
      rw [mem, word]
      exact h.counter
    · rw [mem, status_word _ _ _ (j := 1) (by decide)]
      exact h.width
    · rw [mem, status_word _ _ _ (j := 2) (by decide)]
      exact h.entropy
    · intro j member
      have bounds : j < 16 ∧ j ≠ 13 := by
        simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at member
        omega
      rw [mem, lowWord_store (i := 13) _ _ _ (by decide) bounds.1, ite_eq_right bounds.2]
      exact h.saved j member
  · rw [mem, lowWord_store (i := 13) _ _ _ (by decide) (by decide)]
    rfl

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/Reject.lean`, which only this module imported.
section

/-! Complete native rejection: advance entropy, subtract one u64 attempt and continue. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

theorem SearchLive.reject {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (positive : 0 < remaining) (post : CandidatePost p used s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.reject) s fun t =>
      (SearchLive p (used + candidateUsed p used) (remaining - 1) t ∧
        lowWord t.mem p.control 13 = 4#32) ∧ Rest [.r9, .r10, .r11, .r12] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.reject
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (h.reject_head (candidateUsed_bound p used) post.consumed_low) ?_
  rintro u ⟨liveU, restU⟩
  rw [WP.block_append_iff]
  refine WP.mono (liveU.decrement positive) ?_
  rintro v ⟨liveV, restV⟩
  refine WP.mono liveV.again ?_
  rintro t ⟨⟨live, status⟩, restT⟩
  exact ⟨⟨live, status⟩, (restU.trans (restV.mono (by simp))).trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/Short.lean`, which only this module imported.
section

/-! An incomplete candidate either requests more entropy or exhausts its native entropy budget. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm

theorem SearchLive.short {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (positive : 0 < remaining)
    (candidate : candidateResult p used = none)
    (zero : Spec.Rsa.bytesAt s.mem (State.addr p.c.out) p.c.length = List.replicate p.c.length 0) :
    WP isa VG.Impl.Ffdh.Arm.ParameterSearch.short s fun t =>
      SearchDone p (p.tail used remaining) t ∧ Rest searchClobbers s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.short
  refine WP.seq (WP.mono h.entropy_guard fun u ⟨⟨live, flag, mem⟩, restU⟩ => ?_)
  refine WP.ite _ (by change some u.z = _; rw [flag]) ?_ ?_
  · intro short
    have short' := of_decide_eq_true short
    have zeroU : Spec.Rsa.bytesAt u.mem (State.addr p.c.out) p.c.length = List.replicate p.c.length 0 := by
      rw [mem]; exact zero
    refine WP.mono (live.request_done zeroU) ?_
    rintro t ⟨done, restT⟩
    rw [p.tail_short positive candidate, ite_eq_right (by omega)]
    exact ⟨done, (restU.mono (by simp [searchClobbers])).trans restT⟩
  · intro full
    have full' := of_decide_eq_false full
    refine WP.mono live.exhausted ?_
    rintro t ⟨done, restT⟩
    rw [p.tail_short positive candidate, ite_eq_left (by omega)]
    exact ⟨done, (restU.mono (by simp [searchClobbers])).trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/Classify.lean`, which only this module imported.
section

/-! The native classifier dispatches exactly the shared candidate's three possible results. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

def Classified (p : SearchParams) (used remaining : Nat) (s : State) : Prop :=
  match candidateResult p used with
  | some (none, _) => SearchLive p (used + candidateUsed p used) (remaining - 1) s ∧
      lowWord s.mem p.control 13 = 4#32
  | _ => SearchDone p (p.tail used remaining) s

theorem SearchLive.classify {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (positive : 0 < remaining) (post : CandidatePost p used s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterSearch.classify s fun t =>
      Classified p used remaining t ∧ Rest searchClobbers s t := by
  have small : Proof.Ffdh.candidateStatus (candidateResult p used) < 3 := by
    cases candidateResult p used with
    | none => decide
    | some pair =>
      obtain ⟨prime, rand⟩ := pair
      cases prime <;> simp only [Proof.Ffdh.candidateStatus] <;> decide
  have native : s.gpr .r0 = BitVec.ofNat 32 (Proof.Ffdh.candidateStatus (candidateResult p used)) := by
    rw [← post.status, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.classify
  refine WP.seq (WP.mono (compareResult_ok s small (Or.inl rfl) native) fun u ⟨⟨flag, mem⟩, rest⟩ => ?_)
  have liveU := h.after_read (by decide) mem rest
  have postU := post.after_read mem rest (by decide)
  have nativeU := (rest.gpr .r0 (by simp)).trans native
  cases result : candidateResult p used with
  | none =>
    simp only [result, Proof.Ffdh.candidateStatus] at flag
    refine WP.ite false (by change some u.z = _; rw [flag]; rfl) (by intro bad; cases bad) ?_
    intro _
    refine WP.seq (WP.mono (compareResult_ok u small (Or.inr rfl) nativeU) fun v ⟨⟨flagV, memV⟩, restV⟩ => ?_)
    have liveV := liveU.after_read (by decide) memV restV
    have postV := postU.after_read memV restV (by decide)
    simp only [result, Proof.Ffdh.candidateStatus] at flagV
    refine WP.ite false (by change some v.z = _; rw [flagV]; rfl) (by intro bad; cases bad) ?_
    intro _
    have zero := postV.output
    rw [result] at zero
    refine WP.mono (liveV.short positive result zero) ?_
    rintro t ⟨done, restT⟩
    exact ⟨by simpa only [Classified, result] using done,
      ((rest.trans restV).mono (by simp)).trans restT⟩
  | some pair =>
    obtain ⟨prime, rand⟩ := pair
    cases prime with
    | none =>
      simp only [result, Proof.Ffdh.candidateStatus] at flag
      refine WP.ite false (by change some u.z = _; rw [flag]; rfl) (by intro bad; cases bad) ?_
      intro _
      refine WP.seq (WP.mono (compareResult_ok u small (Or.inr rfl) nativeU) fun v ⟨⟨flagV, memV⟩, restV⟩ => ?_)
      have liveV := liveU.after_read (by decide) memV restV
      have postV := postU.after_read memV restV (by decide)
      simp only [result, Proof.Ffdh.candidateStatus] at flagV
      refine WP.ite true (by change some v.z = _; rw [flagV]; rfl) ?_ (by intro bad; cases bad)
      intro _
      refine WP.mono (liveV.reject positive postV) ?_
      rintro t ⟨data, restT⟩
      exact ⟨by simpa only [Classified, result] using data,
        ((rest.trans restV).mono (by simp)).trans (restT.mono (by simp [searchClobbers]))⟩
    | some prime =>
      simp only [result, Proof.Ffdh.candidateStatus] at flag
      refine WP.ite true (by change some u.z = _; rw [flag]; rfl) ?_ (by intro bad; cases bad)
      intro _
      refine WP.mono (liveU.accept postU result) ?_
      rintro t ⟨done, restT⟩
      refine ⟨?_, (rest.mono (by simp)).trans (restT.mono (by simp [searchClobbers]))⟩
      simpa only [Classified, result, p.tail_accept positive result] using done

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm

theorem SearchLive.step (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (positive : 0 < remaining) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.candidateStep (.call backend.candidateName backend.candidate)) s
      fun t => Classified p used remaining t ∧ Rest searchClobbers s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.candidateStep
  refine WP.seq (WP.mono h.length_guard fun u ⟨⟨live, flag, _⟩, rest⟩ => ?_)
  refine WP.ite _ (by change some u.z = _; rw [flag]) ?_ ?_
  · intro short
    have short' := of_decide_eq_true short
    have noCandidate := candidate_short p used short'
    have entropy : p.c.bytes.length - used < Spec.Ffdh.parameterEntropy p.c.bits := by
      have width := p.width_bounds
      unfold Spec.Ffdh.parameterEntropy
      change p.c.bytes.length - used < 32769 * p.c.length
      omega
    refine WP.mono live.short_request ?_
    rintro t ⟨done, restT⟩
    refine ⟨?_, (rest.mono (by simp [searchClobbers])).trans restT⟩
    simpa only [Classified, noCandidate, p.tail_short positive noCandidate,
      ite_eq_right (by omega : ¬ Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.bytes.length - used), requestResult] using done
  · intro enough
    have room : used + p.c.length ≤ p.c.bytes.length := by
      have := of_decide_eq_false enough
      have := h.usedBound
      omega
    refine WP.seq (WP.mono (candidateRun_ok backend live room) fun v ⟨⟨liveV, post⟩, restV⟩ => ?_)
    refine WP.mono (liveV.classify positive post) ?_
    rintro t ⟨data, restT⟩
    exact ⟨data, ((rest.mono (by simp [searchClobbers])).trans restV).trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
