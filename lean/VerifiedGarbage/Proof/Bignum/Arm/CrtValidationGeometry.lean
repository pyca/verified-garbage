module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductGeometry
public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidateProduct
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Comparison-buffer bounds for private RSA factor validation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

theorem CrtShared.pad_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    CrtPadInput g.base g.size (workspaceWords g.words) g.words (modulusOffset g.words) s := by
  refine ⟨h.buffers.workspace, h.buffers.context.main, h.main.toCrtLayoutState, ?_,
    Nat.le_trans (crt_modulus_end_le _) h.buffers.storageFits, ready.ptr, h.main.modulus, ready.stackRead,
    h.stack.separate.sub_left (Region.sub_prefix (by decide)), ready.saved⟩
  simp only [modulusOffset, compareOffset, productOffset, stride]
  omega

theorem CrtShared.compare_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    CrtCompareInput g.base g.size (compareOffset g.words) (productOffset g.words) (modulusOffset g.words) g.words s := by
  have size := h.buffers.storageFits
  have small : 244 ≤ g.size := by
    have fit := h.buffers.context.main.nowrap
    have size' := h.main.toCrtLayoutState.size
    simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productOffset, stride] at size
    omega
  refine ⟨h.buffers.workspace, small, ?_, ready.ptr,
    h.main.toCrtLayoutState.nativeCount h.buffers.context.main, h.main.compare, h.main.product,
    h.main.modulus, ready.stackRead, h.stack.separate.sub_left (Region.sub_prefix (by decide)), ready.saved⟩
  refine ⟨h.buffers.workspace.nowrap, ?_, ?_, Nat.le_trans (crt_modulus_end_le _) size, ?_, ?_,
    h.buffers.workspace.writable⟩
  all_goals simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productBytes, productWords] at size ⊢
  · omega
  · omega
  · right; omega
  · left; omega

theorem CrtShared.validate_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    CrtValidateInput g.base g.size (workspaceWords g.words) (productOffset g.words)
      (compareOffset g.words) (modulusOffset g.words) (crtProductA g.words false) (crtProductB g.words)
      (pOffset g.words) (qOffset g.words) g.words s := by
  refine ⟨h.product_input ready false, ⟨h.pad_input ready, h.compare_input ready, ?_⟩, ?_⟩
  · left
    simp only [modulusOffset, compareOffset, productBytes, productWords]
    omega
  · simp only [productOffset, stride]; omega

end VG.Proof.Bignum.Arm
