module
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots

import VerifiedGarbage.Proof.Rsa.Arm.PrivStackWord
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Retain the exponent and input arguments before the CRT call -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

theorem argument_slot {g : PrivGeometry} {j : Nat} (hj : j < 3) :
    g.argument j = slotValue g (j + 3) := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> rfl

theorem saveIncomingSlot_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) {j : Nat} (hj : j < 3) (ptr : s.gpr .r12 = g.stack) :
    WP isa (.block (saveIncomingSlot j)) s fun t => PrivContext g bs t ∧
      t.mem = s.mem.writeW (off (State.addr g.stack) (76 + 4 * j)) (slotValue g (j + 3)) ∧
      Frame [g.innerRegion] s.mem t.mem ∧ Rest [.r0] s t := by
  have fit := h.valid.stackHigh
  unfold saveIncomingSlot
  refine wp_loadStack (a := off (State.addr g.stack) (arg j))
    (by simp only [arg, frameBytes]; omega)
    (by rw [h.sp]; exact addr_add (by simp only [arg, frameBytes] at *; omega))
    (h.readArg (by omega)) fun u a => ?_
  refine wp_str (a := off (State.addr g.stack) (76 + 4 * j)) (by simp only [oE]; omega)
    (by rw [a.other .r12 (by decide), ptr]; exact addr_add (by simp only [frameBytes, oE] at *; omega))
    (by rw [a.wr]; exact h.inner.write (by simp only [frameBytes]; omega)) fun t b => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off (State.addr g.stack) (76 + 4 * j)) (slotValue g (j + 3)) := by
    rw [b.mem, a.gpr, a.mem, h.arguments j (by omega), argument_slot hj]
  have rest : Rest [.r0] s t := (a.rest (by simp)).trans (b.rest _)
  have frame : Frame [g.innerRegion] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by simp only [frameBytes]; omega) (by omega))
  exact ⟨h.after (frame.mono (by simp [bodyWrites])) rest, mem, frame, rest⟩

theorem saveIncoming_prefix_ok (n : Nat) (hn : n ≤ 3) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s)
    (slots : ∀ i < 3, s.mem.readW (off (State.addr g.stack) (64 + 4 * i)) 32 = slotValue g i)
    (ptr : s.gpr .r12 = g.stack) :
    WP isa (.block ((List.range n).flatMap saveIncomingSlot)) s fun t => PrivContext g bs t ∧
      (∀ i < n + 3, t.mem.readW (off (State.addr g.stack) (64 + 4 * i)) 32 = slotValue g i) ∧
      Frame [g.innerRegion] s.mem t.mem ∧ Rest [.r0] s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨h, slots, Frame.refl _ _, Rest.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h slots ptr) ?_
    rintro u ⟨hu, retained, frameU, restU⟩
    refine WP.mono (saveIncomingSlot_ok u hu (by omega : n < 3)
      ((restU.gpr .r12 (by simp)).trans ptr)) ?_
    rintro t ⟨ht, mem, frameT, restT⟩
    refine ⟨ht, ?_, frameU.trans frameT, restU.trans restT⟩
    intro i hi
    by_cases same : i = n + 3
    · subst i
      have address : 64 + 4 * (n + 3) = 76 + 4 * n := by omega
      rw [mem, address, Mem.readW_writeW_self32]
    · have outside := writeW32_outside u.mem (State.addr g.stack) (d := 76 + 4 * n)
        (slotValue g (n + 3)) (by omega)
      rw [mem, outside_read32 outside (d := 64 + 4 * i) (by omega) (by omega)]
      exact retained i (by omega)
end VG.Proof.Rsa.Arm
