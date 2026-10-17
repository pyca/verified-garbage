module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedFrame
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCall
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Read the q-workspace pointer without modifying the active workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr)

theorem CrtShared.of_mem {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtShared g bs s) (mem : t.mem = s.mem) (rest : Rest rs s t) : CrtShared g bs t := by
  apply h.after_external (regions := []) (by rw [mem]; exact Frame.refl _ _) rest
  · simp
  · simp

theorem crt_qSource_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
    WP isa (.block CrtFn.qSource) s fun t => t.gpr .r1 = crtQ g.base g.words ∧
      t.mem = s.mem ∧ Rest [.r1] s t := by
  unfold CrtFn.qSource
  refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
    (addr_add (by have := h.stack.nowrap; omega)) (h.stack.read (by decide)) fun u a => ?_
  refine wp_ldr (a := off (State.addr g.base) 228) (by decide)
    (by rw [a.gpr, h.savedMain]; exact addr_add (by have := h.buffers.context.main.nowrap; have := h.buffers.context.size; omega))
    (by rw [a.rd, a.wr]; exact h.buffers.context.main.read (by have := h.buffers.context.size; omega)) fun t b => WP.block_nil ?_
  exact ⟨by rw [b.gpr, a.mem]; exact h.main.q, b.mem.trans a.mem, (a.rest (by simp)).trans (b.rest (by simp))⟩

end VG.Proof.Bignum.Arm
