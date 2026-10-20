module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState

import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Set the byte-export pointers and public output length -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr)

def crtProduct (base : BitVec 32) (w : Nat) : BitVec 32 := base + BitVec.ofNat 32 (productOffset w)

theorem crt_outputArgs_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ptr : s.gpr .r0 = g.base) :
    WP isa (.block CrtFn.outputArgs) s fun t => t.gpr .r1 = crtProduct g.base g.words ∧
      t.gpr .r4 = g.output ∧ t.gpr .r6 = BitVec.ofNat 32 g.length ∧
      t.mem = s.mem ∧ Rest [.r1, .r4, .r6] s t := by
  unfold CrtFn.outputArgs
  refine wp_ldr (a := off (State.addr g.base) 232) (by decide)
    (by rw [ptr]; exact addr_add (by have := h.buffers.context.main.nowrap; have := h.buffers.context.size; omega))
    (h.buffers.context.main.read (by have := h.buffers.context.size; omega)) fun u a => ?_
  refine wp_loadStack (a := off (State.addr s.sp) 4) (by decide)
    (by rw [a.sp]; exact addr_add (by have := h.stack.nowrap; omega))
    (by rw [a.rd, a.wr]; exact h.stack.read (by decide)) fun v b => ?_
  refine wp_loadStack (a := off (State.addr s.sp) 12) (by decide)
    (by rw [b.sp, a.sp]; exact addr_add (by have := h.stack.nowrap; omega))
    (by rw [b.rd, b.wr, a.rd, a.wr]; exact h.stack.read (by decide)) fun t c => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, c.mem.trans (b.mem.trans a.mem),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans (c.rest (by simp)))⟩
  · rw [c.other .r1 (by decide), b.other .r1 (by decide), a.gpr]; exact h.main.product
  · rw [c.other .r4 (by decide), b.gpr, a.mem]; exact h.stack.output
  · rw [c.gpr, b.mem, a.mem]; exact h.stack.count

end VG.Proof.Bignum.Arm
