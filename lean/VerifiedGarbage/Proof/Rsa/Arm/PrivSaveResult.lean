module
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots

import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Retain a callee's status without touching arguments or private buffers -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

theorem saveResult_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) {d : Nat} (low : 88 ≤ d) (high : d + 4 ≤ 96) :
    WP isa (.block (saveResult d)) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      t.gpr .r12 = g.stack ∧ t.mem = s.mem.writeW (off (State.addr g.stack) d) (s.gpr .r0) ∧
      Frame [⟨off (State.addr g.stack) d, 4⟩] s.mem t.mem ∧ Rest [.r12] s t := by
  unfold saveResult
  refine wp_stackAddr (by decide) fun u a => ?_
  have ptr : u.gpr .r12 = g.stack := by simpa only [BitVec.add_zero, h.sp] using a.gpr
  refine wp_str (a := off (State.addr g.stack) d) (by omega)
    (by rw [ptr]; exact addr_add (by have := h.valid.stackHigh; simp only [frameBytes] at *; omega))
    (by rw [a.wr]; exact h.inner.write (by simp only [frameBytes]; omega)) fun t b => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off (State.addr g.stack) d) (s.gpr .r0) := by
    rw [b.mem, a.mem, a.other .r0 (by decide)]
  have frame : Frame [⟨off (State.addr g.stack) d, 4⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have rest : Rest [.r12] s t := (a.rest (by simp)).trans (b.rest _)
  refine ⟨h.after (frame.sub ?_) rest, slots.after frame ?_, (congrFun b.gpr .r12).trans ptr, mem, frame, rest⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by simp only [frameBytes]; omega)⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact Offset.disjoint _ (Or.inl (by omega)) (by decide) (by omega)
end VG.Proof.Rsa.Arm
