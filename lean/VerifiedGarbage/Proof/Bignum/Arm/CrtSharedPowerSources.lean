module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPowerSources
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout

/-! # Recover ciphertext and exponent arguments in either selected factor workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

theorem CrtShared.power_sources {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    (h : CrtShared g bs s) (i : Fin 6) (exponent : i = 3 ∨ i = 4)
    (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words) :
    CrtPowerSources child g.input (g.source i.succ) (workspaceWords g.words) g.words g.length
      (g.sourceLength i.succ) (56 + 8 * i.val) (bs 1) (bs i.succ) s := by
  have sub := crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member
  refine ⟨⟨h.stack.nowrap, ⟨h.stack.read (by decide), h.stack.read (by decide),
    h.stack.read (by have := i.isLt; omega), h.stack.read (by have := i.isLt; omega)⟩, h.stack.separate.sub_right sub, by have := i.isLt; omega,
    h.stack.pointer 0, h.stack.count, h.stack.pointer i, ?_⟩,
    h.buffers.source 1, h.buffers.source i.succ, (h.buffers.sourceSeparate 1).sub_right sub,
    (h.buffers.sourceSeparate i.succ).sub_right sub,
    by have := h.buffers.lengthValid.1; omega, (crt_width_valid h.buffers.lengthValid).2.2, ?_, ?_⟩
  · simpa only [show 56 + 8 * i.val + 4 = 60 + 8 * i.val by omega] using h.stack.length i
  · rcases exponent with rfl | rfl
    · exact h.buffers.pPositive
    · exact h.buffers.qPositive
  · have length := h.buffers.lengthValid.2
    rcases exponent with rfl | rfl
    · change g.pLength < _; have := h.buffers.pShort; omega
    · change g.qLength < _; have := h.buffers.qShort; omega

end VG.Proof.Bignum.Arm
