module

public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.Offset

/-! Installing an argument slot retains every previously installed argument. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem ArgumentMemory.store_slot {p : Inputs} {slots : List Nat} {s t : State} {rs : List Reg}
    (h : ArgumentMemory p slots s) (stable : stableSlots slots = true) (d : Nat)
    (aligned : d % 4 = 0) (fit : d + 4 ≤ 72)
    (mem : t.mem = s.mem.writeW (off (State.addr s.sp) d) (p.slotValue d))
    (rest : Rest rs s t) : ArgumentMemory p (d :: slots) t := by
  have frame : Frame [⟨off (State.addr s.sp) d, 4⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have domainSep (r : Region) (hr : r ∈ [⟨off (State.addr s.sp) d, 4⟩]) :
      (⟨State.addr p.domain, p.dom.length⟩ : Region).Disjoint r := by
    rw [List.mem_singleton] at hr
    subst r
    exact h.domainStack.sub_right (Offset.sub_base _ fit)
  refine ⟨h.workspace.congr rest.wr, h.locals.after rest, h.domain.after_frame frame rest domainSep,
    by rw [rest.sp]; exact h.domainStack, ?_⟩
  intro e he
  rw [rest.sp]
  by_cases same : e = d
  · subst e
    rw [mem, Mem.readW_writeW_self32]
  · have old : e ∈ slots := by
      simp only [List.mem_cons] at he
      exact he.resolve_left same
    have bounds := stableSlots_at stable old
    have item := List.all_eq_true.mp stable e old
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at item
    rw [mem, Mem.readW_writeW_sep (Offset.sep (State.addr s.sp) (by omega) (by omega) (by omega)) (by decide)]
    exact h.saved e old

theorem Context.store_slot {p : Inputs} {slots : List Nat} {s t : State} {rs : List Reg}
    (h : Context p slots s) (stable : stableSlots slots = true) (d : Nat)
    (aligned : d % 4 = 0) (fit : d + 4 ≤ 72)
    (mem : t.mem = s.mem.writeW (off (State.addr s.sp) d) (p.slotValue d))
    (rest : Rest rs s t) (ptr : t.gpr .r0 = p.base) : Context p (d :: slots) t :=
  ⟨h.toArgumentMemory.store_slot stable d aligned fit mem rest, ptr⟩

end VG.Proof.Ffdh.Arm
