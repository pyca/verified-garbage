module

public import VerifiedGarbage.Impl.Ffdh.Arm.VettedCap
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! Store any selected width and mask while preserving the common saved arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedCap
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem load_ok (s : State) {p : Inputs} {slots : List Nat} (h : Context p slots s) :
    WP isa (.block VG.Impl.Ffdh.Arm.VettedCap.load) s fun t =>
      (t.gpr .r6 = s.mem.readW (off (State.addr s.sp) 20) 32 ∧
        t.gpr .r3 = s.mem.readW (off (State.addr s.sp) 68) 32 ∧ t.mem = s.mem) ∧
      Rest [.r3, .r6] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) : State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have r20 := h.locals.read (d := 20) (by decide)
  have r68 := h.locals.read (d := 68) (by decide)
  refine withRest [.r3, .r6] ?_ (by
    intro r hr i hi
    simp only [instrs, VG.Impl.Ffdh.Arm.VettedCap.load, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> cases r <;> simp_all [clobbers, dstOf]) (by rfl)
  unfold VG.Impl.Ffdh.Arm.VettedCap.load
  ffrun [addr 20 (by decide), addr 68 (by decide), r20, r68]

theorem save_store (s : State) {p : Inputs} {slots : List Nat} (h : Context p slots s) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr s.sp) 20) (s.gpr .r6)).writeW
        (off (State.addr s.sp) 68) (s.gpr .r3) ∧ Rest [.r12] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) : State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have w20 := h.locals.space.write (off := 20) (by decide)
  have w68 := h.locals.space.write (off := 68) (by decide)
  refine withRest [.r12] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave VG.Impl.Ffdh.Arm.Domain.st
  ffrun [addr 20 (by decide), addr 68 (by decide), w20, w68, BitVec.add_zero, off]

theorem save_ok (s : State) {p : Inputs} {slots : List Nat} (h : Context p slots s)
    (common : sampleSlots slots) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave) s fun t =>
      Context p slots t ∧ t.mem.readW (off (State.addr t.sp) 20) 32 = s.gpr .r6 ∧
      t.mem.readW (off (State.addr t.sp) 68) 32 = s.gpr .r3 ∧
      Frame [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩] s.mem t.mem ∧ Rest [.r12] s t := by
  refine WP.mono (save_store s h) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩] s.mem t.mem := by
    rw [mem]
    exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
      (by simp) _ (Region.contains_self _ _)
  have ctx : Context p slots t := by
    refine h.after_frame frame rest ((rest.gpr .r0 (by simp)).trans h.ptr) ?_ ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.domainStack.sub_right (Offset.sub_base _ (by decide : 20 + 4 ≤ 72))
      · exact h.domainStack.sub_right (Offset.sub_base _ (by decide : 68 + 4 ≤ 72))
    · intro d hd r hr
      have bounds := common d hd
      have nowrap := h.locals.space.nowrap
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine ⟨ctx, ?_, ?_, frame, rest⟩
  · rw [rest.sp, mem, Mem.readW_writeW_sep (Offset.sep (State.addr s.sp) (d := 20) (n := 4) (e := 68) (k := 4) (by decide)
      (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  · rw [rest.sp, mem, Mem.readW_writeW_self32]

end VG.Proof.Ffdh.Arm.VettedCap
