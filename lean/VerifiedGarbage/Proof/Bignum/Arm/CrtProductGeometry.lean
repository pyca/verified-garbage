module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.Bignum.Arm.CrtCoefficient

/-! # Derive exact wide-product inputs from the live CRT workspace layouts -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)

def crtProductA (w : Nat) (coefficient : Bool) : Nat := pOffset w + arrAt w (if coefficient then 5 else 0)
def crtProductB (w : Nat) : Nat := qOffset w + arrAt w 0

theorem CrtShared.product_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) (coefficient : Bool) :
    CrtProductInput g.base g.size (productOffset g.words) (crtProductA g.words coefficient) (crtProductB g.words)
      (pOffset g.words) (qOffset g.words) g.words s coefficient := by
  let w := g.words
  let j : Nat := if coefficient then 5 else 0
  have hj : j < 8 := by cases coefficient <;> decide
  have slot : 64 + 8 * j = productOperandSlot coefficient := by cases coefficient <;> rfl
  have size := h.buffers.storageFits
  have width := h.buffers.context.width
  have endA := Nat.le_trans (array_end_le (w := w) hj) h.buffers.context.arraysFit
  have endB := Nat.le_trans (array_end_le (w := w) (by decide : 0 < 8)) h.buffers.context.arraysFit
  have strideEq : 8 * workspaceWords w = stride w := rfl
  rw [strideEq] at endA endB
  have linear : 3 * stride w + 3 * (16 * w + 8) ≤ g.size := by
    have size0 : 3 * stride w + 4 * (4 * w + 2) + 4 * (4 * w + 2) + 4 * (4 * w + 2) + stride w ≤ g.size := size
    omega
  have stridePos : 384 ≤ stride w := by simp only [VG.Impl.Bignum.Arm.Crt.stride, workspaceWords]; omega
  have aHeader : 256 ≤ arrAt w j := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega
  have bHeader : 256 ≤ arrAt w 0 := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega
  have wide : WideProductCtx s g.base g.size (productOffset w) (crtProductA w coefficient) (crtProductB w) (2 * w) (2 * w) := by
    refine ⟨h.buffers.workspace, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ready.stackRead, h.stack.separate.sub_left (Region.sub_prefix (by decide)), ready.saved⟩
    all_goals simp only [crtProductA, crtProductB, pOffset, qOffset, productOffset]
    · change 256 ≤ stride w + arrAt w j; omega
    · omega
    · omega
    · change stride w + arrAt w j + 4 * (2 * w) ≤ g.size; omega
    · omega
    · omega
    · right; change stride w + arrAt w j + 4 * (2 * w) ≤ 3 * stride w; omega
    · right; omega
  obtain ⟨paddr, qaddr, _, _⟩ := crt_storage_addresses h.buffers.workspace h.buffers.storageFits
  have ph := nativeHeader_of_layout s.mem (crtP g.base w) h.buffers.context.p.nowrap (Nat.le_refl _) h.p.layout
  have qh := nativeHeader_of_layout s.mem (crtQ g.base w) h.buffers.context.q.nowrap (Nat.le_refl _) h.q.layout
  rw [h.p.width] at ph
  rw [h.q.width] at qh
  have pArray := ph.array j hj
  have qArray := qh.array 0 (by decide)
  change s.mem.readW (off (State.addr (crtP g.base w)) (64 + 8 * j)) 32 = _ at pArray
  rw [paddr] at pArray
  simp only [off, Offset.add_add, slot] at pArray
  change s.mem.readW (off (State.addr (crtQ g.base w)) 64) 32 = _ at qArray
  rw [qaddr] at qArray
  simp only [off, Offset.add_add] at qArray
  refine ⟨wide, by omega, by change 256 ≤ stride w; omega, by change 256 ≤ 2 * stride w; omega,
    ?_, by change 2 * stride w + 68 ≤ 3 * stride w; omega, ready.ptr, h.main.p, h.main.q,
    ?_, ?_, h.main.product, h.main.toCrtLayoutState.nativeCount h.buffers.context.main⟩
  · change stride w + productOperandSlot coefficient + 4 ≤ 3 * stride w
    cases coefficient <;> simp only [productOperandSlot, Bool.false_eq_true, ↓reduceIte] <;> omega
  · simpa only [crtP, off, Offset.add_add, crtProductA, j] using pArray
  · simpa only [crtQ, off, Offset.add_add, crtProductB] using qArray

end VG.Proof.Bignum.Arm
