module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.Bignum.Arm.CrtCoefficient
public import VerifiedGarbage.Proof.Bignum.Arm.WideProductState
public import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct
import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWide
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Bignum.Arm.CrtProductState`, which this module and modules that import it used -/

section

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
  refine WP.mono (crt_clearWide_ok s h.workspace (by omega_using [headerFit]) (by omega_using [headerFit] : 232 + 4 ≤ size) (by decide)
    (by omega_using [outFit]) h.ptr h.count h.product h.stackRead h.stackSep h.saved) ?_
  rintro t ⟨zero, outside, frame, ptr, rest⟩
  rw [show 4 * w + 2 = 2 * w + 2 * w + 2 by omega_using []] at zero outside
  refine ⟨⟨h.toWideProductCtx.after_frame rest frame, h.parentFit, h.pHeader, h.qHeader, beforeP, beforeQ, ptr, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    zero, outside, frame, rest⟩
  · rw [outside_read32 outside (d := 224) (by omega_using [head]) (by decide)]; exact h.pLink
  · rw [outside_read32 outside (d := 228) (by omega_using [head]) (by decide)]; exact h.qLink
  · rw [outside_read32 outside (d := cp + productOperandSlot coefficient) (by omega_using [beforeP]) (by omega_using [outFit, beforeP, nowrap])]; exact h.pArray
  · rw [outside_read32 outside (d := cq + 64) (by omega_using [beforeQ]) (by omega_using [outFit, beforeQ, nowrap])]; exact h.qArray
  · rw [outside_read32 outside (d := 232) (by omega_using [head]) (by decide)]; exact h.product
  · rw [outside_read32 outside (d := 48) (by omega_using [head]) (by decide)]; exact h.count

end VG.Proof.Bignum.Arm

end

end

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
    omega_using [size0]
  have stridePos : 384 ≤ stride w := by simp only [VG.Impl.Bignum.Arm.Crt.stride, workspaceWords]; omega_using []
  have aHeader : 256 ≤ arrAt w j := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []
  have bHeader : 256 ≤ arrAt w 0 := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []
  have wide : WideProductCtx s g.base g.size (productOffset w) (crtProductA w coefficient) (crtProductB w) (2 * w) (2 * w) := by
    refine ⟨h.buffers.workspace, by omega, by omega, by omega_using [linear, stridePos], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ready.stackRead, h.stack.separate.sub_left (Region.sub_prefix (by decide)), ready.saved⟩
    all_goals simp only [crtProductA, crtProductB, pOffset, qOffset, productOffset]
    · change 256 ≤ stride w + arrAt w j; omega_using [stridePos]
    · omega_using [stridePos]
    · omega_using [stridePos]
    · change stride w + arrAt w j + 4 * (2 * w) ≤ g.size; omega_using [endA, linear]
    · omega_using [endB, linear]
    · omega_using [linear]
    · right; change stride w + arrAt w j + 4 * (2 * w) ≤ 3 * stride w; omega_using [endA]
    · right; omega_using [endB]
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
  refine ⟨wide, by omega_using [linear, stridePos], by change 256 ≤ stride w; omega_using [stridePos], by change 256 ≤ 2 * stride w; omega_using [stridePos],
    ?_, by change 2 * stride w + 68 ≤ 3 * stride w; omega_using [stridePos], ready.ptr, h.main.p, h.main.q,
    ?_, ?_, h.main.product, h.main.toCrtLayoutState.nativeCount h.buffers.context.main⟩
  · change stride w + productOperandSlot coefficient + 4 ≤ 3 * stride w
    cases coefficient <;> simp only [productOperandSlot, Bool.false_eq_true, ↓reduceIte] <;> omega_using [stridePos]
  · simpa only [crtP, off, Offset.add_add, crtProductA, j] using pArray
  · simpa only [crtQ, off, Offset.add_add, crtProductB] using qArray

end VG.Proof.Bignum.Arm
