module
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots

import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Copy one retained argument into the outgoing call area -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

theorem copyRetained_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) {j d : Nat}
    (hj : j < 6) (hd : d + 4 ≤ 56) (ptr : s.gpr .r12 = g.stack) :
    WP isa (.block (copyRetained j d)) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      t.mem = s.mem.writeW (off (State.addr g.stack) d) (slotValue g j) ∧
      Frame [⟨off (State.addr g.stack) d, 4⟩] s.mem t.mem ∧ Rest [.r0] s t := by
  have fit := h.valid.stackHigh
  unfold copyRetained
  refine wp_loadStack (a := off (State.addr g.stack) (64 + 4 * j))
    (by omega)
    (by rw [h.sp]; exact addr_add (by simp only [frameBytes] at *; omega))
    (h.inner.read (by simp only [frameBytes]; omega)) fun u a => ?_
  refine wp_str (a := off (State.addr g.stack) d) (by omega)
    (by rw [a.other .r12 (by decide), ptr]; exact addr_add (by simp only [frameBytes] at *; omega))
    (by rw [a.wr]; exact h.inner.write (by simp only [frameBytes]; omega)) fun t b => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off (State.addr g.stack) d) (slotValue g j) := by
    rw [b.mem, a.gpr, a.mem, slots j hj]
  have rest : Rest [.r0] s t := (a.rest (by simp)).trans (b.rest _)
  have frame : Frame [⟨off (State.addr g.stack) d, 4⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h.after (frame.sub ?_) rest, slots.after frame ?_, mem, frame, rest⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by simp only [frameBytes]; omega)⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact Offset.disjoint _ (Or.inr (by omega)) (by decide) (by omega)
end VG.Proof.Rsa.Arm
