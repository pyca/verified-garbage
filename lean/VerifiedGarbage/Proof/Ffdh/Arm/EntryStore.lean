module

public import VerifiedGarbage.Proof.Ffdh.Arm.StoreSlot
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! Argument stores can precede installing the workspace pointer in r0. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

theorem ArgumentMemory.of_mem {p : Inputs} {slots : List Nat} {s t : State} {rs : List Reg}
    (h : ArgumentMemory p slots s) (mem : t.mem = s.mem) (rest : Rest rs s t) : ArgumentMemory p slots t := by
  have frame : Frame [] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact h.after_frame frame rest (by simp) (by simp)

theorem wp_store_arg {s : State} {p : Inputs} {slots : List Nat} {is : List Instr} {Q : State → Prop}
    (r : Reg) (d : Nat) (h : ArgumentMemory p slots s) (stable : stableSlots slots = true)
    (aligned : d % 4 = 0) (fit : d + 4 ≤ 72) (source : s.gpr r = p.slotValue d)
    (stackBase : s.gpr .r12 = s.sp)
    (next : ∀ t, ArgumentMemory p (d :: slots) t →
      Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem → Rest [] s t → WP isa (.block is) t Q) :
    WP isa (.block (.str r .r12 d :: is)) s Q := by
  refine wp_str (a := off (State.addr s.sp) d) (by omega)
    (by rw [stackBase]; exact addr_add (by have := h.locals.space.nowrap; omega))
    (h.locals.space.write fit) fun t stored => ?_
  have mem : t.mem = s.mem.writeW (off (State.addr s.sp) d) (p.slotValue d) := by rw [stored.mem, source]
  have rest := stored.rest []
  have args := h.store_slot stable d aligned fit mem rest
  apply next t args _ rest
  rw [mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ fit (by omega))

structure IncomingScratch (p : Inputs) (s : State) : Prop where
  fits : s.sp.toNat + 136 ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 132) 4
  value : s.mem.readW (off (State.addr s.sp) 132) 32 = p.base

theorem IncomingScratch.after {p : Inputs} {s t : State} {rs : List Reg} (h : IncomingScratch p s)
    (frame : Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem) (rest : Rest rs s t) : IncomingScratch p t := by
  refine ⟨by rw [rest.sp]; exact h.fits, ?_, ?_⟩
  · rw [rest.rd, rest.wr, rest.sp]; exact h.readable
  · rw [rest.sp]
    have word := frame.readW (w := 32) (r := ⟨off (State.addr s.sp) 132, 4⟩) (Region.contains_self _ _)
      (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact Offset.disjoint_base _ (by decide) (by decide)) (by decide)
    exact word.trans h.value

end VG.Proof.Ffdh.Arm
