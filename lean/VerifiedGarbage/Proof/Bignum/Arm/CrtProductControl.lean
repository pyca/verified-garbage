module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Updating multiplication controls preserves all public CRT buffer links -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Bignum.Arm.Crt
open VG.Proof.X25519.Arm (Rest)

theorem CrtProductInput.after_control {s t : State} {base value : BitVec 32} {size o a b cp cq w d : Nat} {coefficient : Bool}
    (h : CrtProductInput base size o a b cp cq w s coefficient) (hd : 128 ≤ d) (hd' : d + 4 ≤ 148)
    (mem : t.mem = s.mem.writeW (off (State.addr base) d) value) (rest : Rest [.r1] s t) :
    CrtProductInput base size o a b cp cq w t coefficient := by
  have fit := h.parentFit
  have nowrap := h.workspace.nowrap
  have pHeader := h.pHeader
  have qHeader := h.qHeader
  have beforeP := h.pBeforeOut
  have beforeQ := h.qBeforeOut
  have outFit := h.outFits
  have outside := writeW32_outside s.mem (State.addr base) (d := d) value (by omega)
  rw [← mem] at outside
  have frame := outside_workspace outside (size := size) (by omega)
  refine ⟨h.toWideProductCtx.after_frame rest frame, h.parentFit, pHeader, qHeader, beforeP, beforeQ,
    (rest.gpr .r0 (by simp)).trans h.ptr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [outside_read32 outside (d := 224) (by omega) (by decide)]; exact h.pLink
  · rw [outside_read32 outside (d := 228) (by omega) (by decide)]; exact h.qLink
  · rw [outside_read32 outside (d := cp + productOperandSlot coefficient) (by omega) (by omega)]; exact h.pArray
  · rw [outside_read32 outside (d := cq + 64) (by omega) (by omega)]; exact h.qArray
  · rw [outside_read32 outside (d := 232) (by omega) (by decide)]; exact h.product
  · rw [outside_read32 outside (d := 48) (by omega) (by decide)]; exact h.count

end VG.Proof.Bignum.Arm
