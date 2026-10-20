module
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots

import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Pass the private stack temporary as the public-operation input -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

theorem storeTemporary_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) (ptr : s.gpr .r12 = g.stack) :
    WP isa (.block storeTemporary) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      t.mem = s.mem.writeW (off (State.addr g.stack) 8) g.temporary ∧
      Frame [⟨off (State.addr g.stack) 8, 4⟩] s.mem t.mem ∧ Rest [.r0] s t := by
  have fit := h.valid.stackHigh
  unfold storeTemporary
  refine wp_stackAddr (by decide) fun u a => ?_
  refine wp_str (a := off (State.addr g.stack) 8) (by decide)
    (by rw [a.other .r12 (by decide), ptr]; exact addr_add (by simp only [frameBytes] at *; omega))
    (by rw [a.wr]; exact h.inner.write (by decide)) fun t b => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off (State.addr g.stack) 8) g.temporary := by
    rw [b.mem, a.gpr, a.mem, h.sp]; rfl
  have rest : Rest [.r0] s t := (a.rest (by simp)).trans (b.rest _)
  have frame : Frame [⟨off (State.addr g.stack) 8, 4⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h.after (frame.sub ?_) rest, slots.after frame ?_, mem, frame, rest⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by decide)⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide)
end VG.Proof.Rsa.Arm
