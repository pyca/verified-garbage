module

public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareArgs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Preserve the caller's arguments while preparing RSA's modulus slots. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def stableSlots (slots : List Nat) : Bool :=
  slots.all fun d => d % 4 == 0 && d ≤ 68 && d != 8 && d != 12

theorem stableSlots_at {slots : List Nat} (h : stableSlots slots = true) {d : Nat} (hd : d ∈ slots) :
    d + 4 ≤ 72 ∧ (d + 4 ≤ 8 ∨ 12 ≤ d) ∧ (d + 4 ≤ 12 ∨ 16 ≤ d) := by
  have item := List.all_eq_true.mp h d hd
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at item
  omega

def prepareWrites (s : State) : List Region :=
  [⟨off (State.addr s.sp) 8, 4⟩, ⟨off (State.addr s.sp) 12, 4⟩]

theorem prepareArgs_ok (s : State) {p : Inputs} {slots : List Nat} (slot : Nat)
    (h : Context p slots s) (stable : stableSlots slots = true)
    (hs : slot ∈ slots) (hk : 32 ∈ slots) (h0 : 0 ∈ slots) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs slot)) s fun t => Context p slots t ∧
      PcStack p.base (s.mem.readW (off (State.addr s.sp) 4) 32) (p.slotValue slot) p.len p.k t ∧
      t.gpr .r4 = p.slotValue slot ∧ t.gpr .r6 = BitVec.ofNat 32 p.k ∧ t.gpr .r12 = s.sp ∧
      Frame (prepareWrites s) s.mem t.mem ∧ Rest [.r4, .r6, .r12] s t := by
  refine WP.mono (prepareArgs_store s slot h hs hk (stableSlots_at stable hs).1) ?_
  rintro t ⟨⟨source, count, stackBase, mem⟩, rest⟩
  have spFit := h.locals.space.nowrap
  have frame : Frame (prepareWrites s) s.mem t.mem := by
    rw [mem]
    exact ((Frame.refl _ _).writeW (by simp [prepareWrites]) _ (Region.contains_self _ _)).writeW
      (by simp [prepareWrites]) _ (Region.contains_self _ _)
  have within (r : Region) (hr : r ∈ prepareWrites s) : r.Sub ⟨State.addr s.sp, 72⟩ := by
    simp only [prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide)
  have domainSep (r : Region) (hr : r ∈ prepareWrites s) := h.domainStack.sub_right (within r hr)
  have savedSep (d : Nat) (hd : d ∈ slots) (r : Region) (hr : r ∈ prepareWrites s) :
      (⟨off (State.addr s.sp) d, 4⟩ : Region).Disjoint r := by
    have bounds := stableSlots_at stable hd
    simp only [prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ bounds.2.1 (by omega) (by decide)
    · exact Offset.disjoint _ bounds.2.2 (by omega) (by decide)
  have context := h.after_frame frame rest ((rest.gpr .r0 (by simp)).trans h.ptr) domainSep savedSep
  have kept4 : t.mem.readW (off (State.addr t.sp) 4) 32 = s.mem.readW (off (State.addr s.sp) 4) 32 := by
    rw [rest.sp]
    apply frame.readW (r := ⟨off (State.addr s.sp) 4, 4⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    simp only [prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by left; decide) (by decide) (by decide)
  have read : InRegions (t.rd ++ t.wr) (State.addr t.sp) 16 := by
    rw [rest.rd, rest.wr, rest.sp]
    refine ⟨⟨State.addr s.sp, 72⟩, List.mem_append_right _ h.locals.space.writable, ?_⟩
    simpa only [off, BitVec.add_zero] using
      (Offset.contains_base (State.addr s.sp) (d := 0) (n := 16) (k := 72) (by decide) (by decide))
  refine ⟨context, ⟨by rw [rest.sp]; omega, read,
    by rw [rest.sp]; exact h.locals.separate.sub_left (Region.sub_prefix (by decide)),
    by simpa only [Inputs.slotValue, off, BitVec.add_zero] using context.saved 0 h0, kept4, ?_, ?_⟩,
    source, count, stackBase, frame, rest⟩
  · rw [rest.sp, mem]
    rw [Mem.readW_writeW_sep (Offset.sep (State.addr s.sp) (by left; decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  · rw [rest.sp, mem, Mem.readW_writeW_self32]

end VG.Proof.Ffdh.Arm
