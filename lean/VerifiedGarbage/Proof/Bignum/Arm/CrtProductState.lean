module
public import VerifiedGarbage.Proof.Bignum.Arm.WideProductState
public import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct

import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWide
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase

/-! # Inputs for exact CRT factor-product validation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtProductInput (base : BitVec 32) (size o a b cp cq w : Nat) (s : State) (coefficient : Bool := false) : Prop
    extends WideProductCtx s base size o a b (2 * w) (2 * w) where
  parentFit : 236 ≤ size
  pHeader : 256 ≤ cp
  qHeader : 256 ≤ cq
  pBeforeOut : cp + productOperandSlot coefficient + 4 ≤ o
  qBeforeOut : cq + 68 ≤ o
  ptr : s.gpr .r0 = base
  pLink : s.mem.readW (off (State.addr base) 224) 32 = base + BitVec.ofNat 32 cp
  qLink : s.mem.readW (off (State.addr base) 228) 32 = base + BitVec.ofNat 32 cq
  pArray : s.mem.readW (off (State.addr base) (cp + productOperandSlot coefficient)) 32 = base + BitVec.ofNat 32 a
  qArray : s.mem.readW (off (State.addr base) (cq + 64)) 32 = base + BitVec.ofNat 32 b
  product : s.mem.readW (off (State.addr base) 232) 32 = base + BitVec.ofNat 32 o
  count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w

theorem WideProductCtx.after_frame {s t : State} {base : BitVec 32} {size o a b m n : Nat}
    (h : WideProductCtx s base size o a b m n) {rs : List Reg}
    (rest : Rest rs s t) (frame : Frame [⟨State.addr base, size⟩] s.mem t.mem) :
    WideProductCtx t base size o a b m n := by
  refine ⟨h.workspace.congr rest.wr, h.positiveA, h.positiveB, h.headerFit, h.aHeader, h.bHeader, h.oHeader,
    h.aFits, h.bFits, h.outFits, h.separateA, h.separateB, ?_, ?_, ?_⟩
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · exact saved_base_kept frame h.stackSep h.saved rest.sp

theorem crt_productClear_ready (s : State) {base : BitVec 32} {size o a b cp cq w : Nat} {coefficient : Bool}
    (h : CrtProductInput base size o a b cp cq w s coefficient) :
    WP isa (clearWide 232) s fun t => CrtProductInput base size o a b cp cq w t coefficient ∧
      val32 t.mem (State.addr base) o (2 * w + 2 * w + 2) = 0 ∧
      Outside (State.addr base) o (4 * (2 * w + 2 * w + 2)) s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have headerFit := h.parentFit
  have outFit := h.outFits
  have head := h.oHeader
  have beforeP := h.pBeforeOut
  have beforeQ := h.qBeforeOut
  have nowrap := h.workspace.nowrap
  refine WP.mono (crt_clearWide_ok s h.workspace (by omega) (by omega : 232 + 4 ≤ size) (by decide)
    (by omega) h.ptr h.count h.product h.stackRead h.stackSep h.saved) ?_
  rintro t ⟨zero, outside, frame, ptr, rest⟩
  rw [show 4 * w + 2 = 2 * w + 2 * w + 2 by omega] at zero outside
  refine ⟨⟨h.toWideProductCtx.after_frame rest frame, h.parentFit, h.pHeader, h.qHeader, beforeP, beforeQ, ptr, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    zero, outside, frame, rest⟩
  · rw [outside_read32 outside (d := 224) (by omega) (by decide)]; exact h.pLink
  · rw [outside_read32 outside (d := 228) (by omega) (by decide)]; exact h.qLink
  · rw [outside_read32 outside (d := cp + productOperandSlot coefficient) (by omega) (by omega)]; exact h.pArray
  · rw [outside_read32 outside (d := cq + 64) (by omega) (by omega)]; exact h.qArray
  · rw [outside_read32 outside (d := 232) (by omega) (by decide)]; exact h.product
  · rw [outside_read32 outside (d := 48) (by omega) (by decide)]; exact h.count

end VG.Proof.Bignum.Arm
