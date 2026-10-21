module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Incoming
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Entry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Memory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.FieldMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Packed
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Argument capture establishes the native search invariant from the persistent public policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

structure SearchStart (p : SearchParams) (s : State) : Prop where
  storage : SearchBuffers p (s.setReg .r4 p.control)
  incoming : EntryArguments p s
  out : s.gpr .r0 = p.c.out
  used : s.gpr .r2 = p.c.usedPtr
  bits : s.gpr .r3 = BitVec.ofNat 32 p.c.bits
  counter : s.mem.readW (State.addr p.control) 64 = BitVec.ofNat 64 p.attempts
  width : s.mem.readW (off (State.addr p.control) 8) 64 = BitVec.ofNat 64 p.c.length
  entropy : s.mem.readW (off (State.addr p.control) 16) 64 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)

theorem SearchStart.entry {p : SearchParams} {s : State} (h : SearchStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.entry) s fun t =>
      SearchLive p 0 p.attempts t ∧ Rest [.r3, .r4] s t := by
  refine WP.mono (entry_ok s h.incoming (h.storage.controller.space.congr rfl) h.out h.used h.bits) ?_
  rintro t ⟨⟨context, mem⟩, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
    rw [mem]; exact VG.Proof.Ffdh.Arm.KeySearch.writeLow_frame _ _ _ (entryValues_bound p)
  have fakeRest : Rest [.r3] (s.setReg .r4 p.control) t := by
    refine ⟨?_, rest.rd, rest.wr, rest.sp⟩
    intro r hr
    by_cases four : r = .r4
    · subst r
      simpa only [State.setReg, ite_true] using context.controller.ptr
    · rw [rest.gpr r (by simp_all), State.setReg]
      simp only [four, ite_false]
  have buffers : SearchBuffers p t := h.storage.after_frame (by decide)
    (frame.mono (by simp [searchRegions])) fakeRest
  have widthLow := packedLow s.mem p.control 1 p.c.length
    (by have := p.width_bounds; omega) h.width
  have entropyLow := packedLow s.mem p.control 2 (Spec.Ffdh.parameterEntropy p.c.bits)
    (by have := p.entropy_bound; omega) h.entropy
  refine ⟨⟨buffers, Nat.zero_le _, Nat.le_refl _, ?_, ?_, ?_, ?_⟩, rest⟩
  · have word := fields_word s.mem p.control (entryValues p) (entryValues_bound p)
      (j := 0) (by decide) (by simp [entryValues])
    have address : off (State.addr p.control) 0 = State.addr p.control := by simp [off]
    rw [show 8 * 0 = 0 from rfl, address] at word
    rw [mem, word]
    exact h.counter
  · rw [mem, fields_word _ _ _ (entryValues_bound p) (j := 1) (by decide) (by simp [entryValues])]
    exact h.width
  · rw [mem, fields_word _ _ _ (entryValues_bound p) (j := 2) (by decide) (by simp [entryValues])]
    exact h.entropy
  · rw [mem]
    exact entry_fields p s.mem widthLow entropyLow

end VG.Proof.Ffdh.Arm.ParameterSearch
