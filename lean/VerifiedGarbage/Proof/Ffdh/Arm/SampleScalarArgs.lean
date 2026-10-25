module

import VerifiedGarbage.Proof.Ffdh.Arm.StoreSlot
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.TCB.Arm.Isa

/-! Set up native entropy cutting and retain the significant scalar pointer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem sampleScalarArgs_ok (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat}
    (h : Context p slots s)
    (width : s.mem.readW (off (State.addr s.sp) 20) 32 = BitVec.ofNat 32 l.width) (h32 : 32 ∈ slots) (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalarArgs) s fun t =>
      (t.gpr .r0 = p.privateValue ∧ t.gpr .r1 = p.entropy ∧ t.gpr .lr = BitVec.ofNat 32 l.lead ∧
        t.gpr .r2 = 0 ∧ t.mem = s.mem.writeW (off (State.addr s.sp) 16) l.start) ∧
      Rest [.r0, .r1, .r2, .r3, .r12, .lr] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have r20 := h.locals.read (d := 20) (by decide)
  have r32 := h.locals.read (d := 32) (by decide)
  have r40 := h.locals.read (d := 40) (by decide)
  have r48 := h.locals.read (d := 48) (by decide)
  have w16 := h.locals.space.write (off := 16) (by decide)
  have leadCount : BitVec.ofNat 32 p.k - BitVec.ofNat 32 l.width = BitVec.ofNat 32 l.lead := by
    rw [Offset.ofNat_sub_ofNat l.width_bounds.2]
    apply congrArg (BitVec.ofNat 32)
    have := l.lead_lt
    unfold ScalarLayout.width
    omega
  refine withRest_all [.r0, .r1, .r2, .r3, .r12, .lr] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalarArgs VG.Impl.Ffdh.Arm.Domain.st
  ffrun [addr 20 (by decide), addr 32 (by decide), addr 40 (by decide), addr 48 (by decide),
    addr 16 (by decide), r20, r32, r40, r48, w16, width, h.saved 32 h32,
    h.saved 40 h40, h.saved 48 h48, Inputs.slotValue, ScalarLayout.start, leadCount, BitVec.add_zero, off]


theorem sampleScalarArgs_retained (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true) (special : sampleSlots slots)
    (width : s.mem.readW (off (State.addr s.sp) 20) 32 = BitVec.ofNat 32 l.width)
    (mask : s.mem.readW (off (State.addr s.sp) 68) 32 = l.mask)
    (h32 : 32 ∈ slots) (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalarArgs) s fun t =>
      SampleMemory p l slots t ∧ t.gpr .r0 = p.privateValue ∧ t.gpr .r1 = p.entropy ∧
      t.gpr .lr = BitVec.ofNat 32 l.lead ∧ t.gpr .r2 = 0 ∧
      Frame [⟨off (State.addr s.sp) 16, 4⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r12, .lr] s t := by
  refine WP.mono (sampleScalarArgs_ok s h width h32 h40 h48) ?_
  rintro t ⟨⟨dst, src, count, zero, mem⟩, rest⟩
  have frame : Frame [⟨off (State.addr s.sp) 16, 4⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have context := h.toArgumentMemory.after_frame frame rest
    (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact h.domainStack.sub_right (Offset.sub_base _ (by decide)))
    (by
      intro d hd r hr
      have er := List.mem_singleton.mp hr; subst r
      have bounds := stableSlots_at stable hd
      have item := List.all_eq_true.mp stable d hd
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at item
      have excluded := special d hd
      exact Offset.disjoint _ (by omega) (by have := h.locals.space.nowrap; omega)
        (by have := h.locals.space.nowrap; omega))
  have keep (d : Nat) (hd : d = 20 ∨ d = 68) :
      t.mem.readW (off (State.addr t.sp) d) 32 = s.mem.readW (off (State.addr s.sp) d) 32 := by
    rw [rest.sp, mem]
    apply Mem.readW_writeW_sep _ (by decide)
    exact Offset.sep _ (by rcases hd with rfl | rfl <;> decide) (by rcases hd with rfl | rfl <;> decide) (by decide)
  refine ⟨⟨context, ?_, (keep 20 (by simp)).trans width, (keep 68 (by simp)).trans mask⟩,
    dst, src, count, zero, frame, rest⟩
  rw [rest.sp, mem, Mem.readW_writeW_self32]

end VG.Proof.Ffdh.Arm
