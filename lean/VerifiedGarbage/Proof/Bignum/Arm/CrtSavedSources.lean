module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Instantiate private operand imports from immutable call arguments -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem CrtShared.savedOperand {g : CrtGeometry} {bs : Fin 7 → List Byte} {s : State} {child : BitVec 32}
    (h : CrtShared g bs s) (i : Fin 6)
    (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words) :
    SavedOperand child (g.source i.succ) (workspaceWords g.words) (g.sourceLength i.succ)
      (56 + 8 * i.val) (60 + 8 * i.val) (bs i.succ) s := by
  have sub := crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member
  exact ⟨h.stack.nowrap, ⟨h.stack.read (by have := i.isLt; omega), h.stack.read (by have := i.isLt; omega)⟩, h.stack.separate.sub_right sub,
    by have := i.isLt; omega, by have := i.isLt; omega, h.stack.pointer i, h.stack.length i,
    h.buffers.source i.succ, (h.buffers.sourceSeparate i.succ).sub_right sub⟩

theorem CrtShared.inputSaved {g : CrtGeometry} {bs : Fin 7 → List Byte} {s : State} {child : BitVec 32}
    (h : CrtShared g bs s)
    (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words) :
    SavedOperand child g.input (workspaceWords g.words) g.length 56 12 (bs 1) s := by
  have sub := crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member
  exact ⟨h.stack.nowrap, ⟨h.stack.read (by decide), h.stack.read (by decide)⟩, h.stack.separate.sub_right sub,
    by decide, by decide, h.stack.pointer 0, h.stack.count,
    h.buffers.source 1, (h.buffers.sourceSeparate 1).sub_right sub⟩

end VG.Proof.Bignum.Arm
