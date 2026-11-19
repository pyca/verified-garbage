module

import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
public import VerifiedGarbage.Impl.Bignum.Arm.CrtValidateProduct
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.CrtCheckProduct
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCompareProduct
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusArgs
public import VerifiedGarbage.Impl.Bignum.Arm.CrtPadModulus
public import VerifiedGarbage.Impl.Bignum.Arm.WideProduct
public import VerifiedGarbage.Proof.Bignum.Arm.WideProductRow
public import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.Bignum.Arm.Zero
import VerifiedGarbage.Impl.Bignum.Arm.HeaderControl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Impl.Bignum.Arm.CrtCoefficient
import VerifiedGarbage.Proof.Bignum.Arm.ByteWords
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedFrame
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState

/-! ### `Bignum.Arm.ControlBuffers`, which this module and modules that import it used -/

section

/-! # Preserve the public layout across writes to control slots and external buffers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (Layout wordAt wOf)

theorem outs_readW {m m' : Mem} {base : Addr} {ranges : List (Nat × Nat)}
    {d bits : Nat} (h : Outs base ranges m m')
    (sep : ∀ r ∈ ranges, d + bits / 8 ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (fit : d + bits / 8 ≤ 2 ^ 64) : m'.readW (off base d) bits = m.readW (off base d) bits := by
  apply Mem.readW_congr
  intro i hi
  apply h
  intro r hr
  rw [ofs_off base (by omega_using [fit, hi])]
  have := sep r hr
  omega_using [hi, this]

theorem CrtLayoutState.of_header_eq {base : BitVec 32} {len w : Nat} {m m' : Mem}
    (h : CrtLayoutState base len w m) (eq : WorkspaceEq (State.addr base) 128 m m') :
    CrtLayoutState base len w m' := by
  have width := eq.width (by decide)
  refine ⟨?_, width.trans h.width⟩
  unfold Layout
  rw [width]
  refine ⟨h.layout.1, h.layout.2.1, h.layout.2.2.1, ?_⟩
  intro j hj
  unfold wordAt
  rw [eq.word (bits := 64) (by simp only [Proof.Rsa.Mont.arrWord]; omega_using [hj])]
  exact h.layout.2.2.2 j hj

theorem control_buffers_header {base : Addr} {m m' : Mem} {ranges : List (Nat × Nat)}
    (h : Outs base ranges m m') (lower : ∀ r ∈ ranges, 128 ≤ r.1) : WorkspaceEq base 128 m m' := by
  refine ⟨fun d k hk => Mem.read_congr ?_⟩
  intro i hi
  apply h
  intro r hr
  rw [ofs_off base (by omega_using [hk, hi])]
  have := lower r hr
  omega_using [hk, hi, this]

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtProductGeometry`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Bignum.Arm.CrtProductValues`, which the modules that import this one used -/

section

/-! ### `Bignum.Arm.CrtValidationPreserved`, which the modules that import this one used -/

section

/-! # Factor validation preserves all three RSA workspace layouts -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

def crtValidationWrites (w : Nat) : List (Nat × Nat) :=
  [(128, 20), (productOffset w, 4 * (4 * w + 2)),
    (modulusOffset w, 4 * (4 * w + 2)), (compareOffset w, 4 * (4 * w + 2))]

theorem WorkspaceEq.of_outs_offset {base child : Addr} {d n : Nat} {ranges : List (Nat × Nat)} {m m' : Mem}
    (address : child = base + BitVec.ofNat 64 d) (fit : d + n < 2 ^ 64)
    (sep : ∀ r ∈ ranges, d + n ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (outside : Outs base ranges m m') : WorkspaceEq child n m m' := by
  refine ⟨fun k bytes hk => Mem.read_congr ?_⟩
  intro i hi
  apply outside
  intro r hr
  rw [address, show off (base + BitVec.ofNat 64 d) k =
    off base (d + k) by simp only [off, Offset.add_add], ofs_off base (by omega_using [fit, hk, hi])]
  have := sep r hr
  omega_using [hk, hi, this]

theorem CrtShared.validation_child_eq {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (outside : Outs (State.addr g.base) (crtValidationWrites g.words) s.mem t.mem) :
    WorkspaceEq (State.addr (crtP g.base g.words)) (8 * workspaceWords g.words) s.mem t.mem ∧
    WorkspaceEq (State.addr (crtQ g.base g.words)) (8 * workspaceWords g.words) s.mem t.mem := by
  obtain ⟨paddr, qaddr, _, _⟩ := crt_storage_addresses h.buffers.workspace h.buffers.storageFits
  have size := h.buffers.storageFits
  have nowrap := h.buffers.workspace.nowrap
  have small := h.main.toCrtLayoutState.size
  have bounds : 3 * stride g.words ≤ g.size := by
    simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productOffset] at size
    omega_using [size]
  constructor
  · apply WorkspaceEq.of_outs_offset paddr (by change stride g.words + stride g.words < _; omega_arith) _ outside
    intro r hr
    simp only [crtValidationWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [pOffset, productOffset, modulusOffset, compareOffset, stride] <;> omega_arith
  · apply WorkspaceEq.of_outs_offset qaddr (by change 2 * stride g.words + stride g.words < _; omega_arith) _ outside
    intro r hr
    simp only [crtValidationWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [qOffset, productOffset, modulusOffset, compareOffset, stride] <;> omega_arith

theorem CrtShared.validation_main {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (outside : Outs (State.addr g.base) (crtValidationWrites g.words) s.mem t.mem) :
    CrtMainState g.base (workspaceWords g.words) g.words t.mem ∧
    numAt t.mem (State.addr g.base) g.words 0 = numAt s.mem (State.addr g.base) g.words 0 := by
  have small := h.main.toCrtLayoutState.size
  have lower (r : Nat × Nat) (hr : r ∈ crtValidationWrites g.words) :
      r = (128, 20) ∨ 3 * stride g.words ≤ r.1 := by
    simp only [crtValidationWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · right; exact Nat.le_refl _
    · right; simp only [modulusOffset, compareOffset, productOffset]; omega_using []
    · right; simp only [compareOffset, productOffset]; omega_using []
  have head := control_buffers_header outside (by
    intro r hr
    rcases lower r hr with rfl | bound
    · exact Nat.le_refl _
    · change 128 ≤ r.1; change 3 * (8 * workspaceWords g.words) ≤ r.1 at bound; omega_using [small, bound])
  have word (d : Nat) (hd : d = 224 ∨ d = 228 ∨ d = 232 ∨ d = 236 ∨ d = 240) :
      t.mem.readW (off (State.addr g.base) d) 32 = s.mem.readW (off (State.addr g.base) d) 32 := by
    apply outs_readW outside
    · intro r hr
      rcases lower r hr with rfl | bound
      · simp only; omega_using [hd]
      · left; change 3 * (8 * workspaceWords g.words) ≤ r.1 at bound; omega_using [small, hd, bound]
    · omega_using [hd]
  refine ⟨⟨h.main.toCrtLayoutState.of_header_eq head,
    (word 224 (by simp)).trans h.main.p, (word 228 (by simp)).trans h.main.q,
    (word 232 (by simp)).trans h.main.product, (word 236 (by simp)).trans h.main.compare,
    (word 240 (by simp)).trans h.main.modulus⟩, ?_⟩
  have end0 := Nat.le_trans (array_end_le (w := g.words) (j := 0) (by decide)) h.buffers.context.arraysFit
  rw [numAt_native, numAt_native]
  apply outside.val32
  · intro r hr
    rcases lower r hr with rfl | bound
    · right; simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []
    · left; change 3 * (8 * workspaceWords g.words) ≤ r.1 at bound; omega_using [end0, bound]
  · have := h.buffers.context.main.nowrap; omega_using [end0, this]

theorem CrtShared.after_validation {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtShared g bs s) (outside : Outs (State.addr g.base) (crtValidationWrites g.words) s.mem t.mem)
    (frame : Frame [⟨State.addr g.base, g.size⟩] s.mem t.mem) (rest : Rest rs s t) :
    CrtShared g bs t := by
  obtain ⟨pEq, qEq⟩ := h.validation_child_eq outside
  obtain ⟨main, modulus⟩ := h.validation_main outside
  exact h.after_frame (frame.mono (by simp [crtLiveMutable])) rest main (h.p.congr pEq) (h.q.congr qEq) modulus

end VG.Proof.Bignum.Arm

end

end

/-! # Interpret native product operands in the shared RSA number model -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)

theorem val32_numAt_offset (m : Mem) (base child : Addr) (d w j : Nat)
    (address : child = base + BitVec.ofNat 64 d) :
    val32 m base (d + arrAt w j) (2 * w) = numAt m child w j := by
  rw [← read_eq_val32, numAt, address, Offset.add_add]
  congr 2 <;> omega_using []

theorem CrtShared.product_values {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (coefficient : Bool) :
    val32 s.mem (State.addr g.base) (crtProductA g.words coefficient) (2 * g.words) =
      numAt s.mem (State.addr (crtP g.base g.words)) g.words (if coefficient then 5 else 0) ∧
    val32 s.mem (State.addr g.base) (crtProductB g.words) (2 * g.words) =
      numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 := by
  obtain ⟨paddr, qaddr, _, _⟩ := crt_storage_addresses h.buffers.workspace h.buffers.storageFits
  exact ⟨val32_numAt_offset _ _ _ _ _ _ paddr, val32_numAt_offset _ _ _ _ _ _ qaddr⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtPadModulus`, which this module and modules that import it used -/

section

/-! # Exact full-width modulus padding for CRT validation -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/ExportPadded.lean`, which only this module imported.
section

/-! # Export a modulus into a zero-padded full-product buffer -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wOf Layout numAt)
open VG.Proof.X25519.Arm (Rest)

theorem exportPadded_ok (s : State) {base : BitVec 32} {len w o d k : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ho : o < 8)
    (fit : base.toNat + d + 4 * (2 * w + k) ≤ 2 ^ 32)
    (write : InRegions s.wr (off (State.addr base) d) (8 * w))
    (sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨off (State.addr base) d, 8 * w⟩)
    (zero : val32 s.mem (State.addr base) (d + 8 * w) k = 0)
    (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o)
    (output : s.gpr .r4 = base + BitVec.ofNat 32 d) :
    WP isa exportArray s fun t =>
      val32 t.mem (State.addr base) d (2 * w + k) = numAt s.mem (State.addr base) w o ∧
      Outside (State.addr base) d (8 * w) s.mem t.mem ∧
      t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := width ▸ layout.1
  have dstAddr : State.addr (base + BitVec.ofNat 32 d) = off (State.addr base) d := addr_add (by omega)
  have dstNat : (base + BitVec.ofNat 32 d).toNat = base.toNat + d := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : base.toNat + d < 2 ^ 32)]
  refine WP.mono (exportArray_ok s ws layout width ho (by rw [dstNat]; omega)
    (by rw [dstAddr]; exact write) (by rw [dstAddr]; exact sep) ptr index output) ?_
  rintro t ⟨value, frame, ptrT, _, rest⟩
  rw [dstAddr] at value frame
  have outside := frame_array_outside (by omega : d + 8 * w < 2 ^ 64) frame
  have high := outside.val32 (d := d + 8 * w) (k := k) (by omega) (by omega)
  have low : val32 t.mem (State.addr base) d (2 * w) = numAt s.mem (State.addr base) w o := by
    rw [← read_eq_val32, show 4 * (2 * w) = 8 * w by omega, value]
    rfl
  refine ⟨?_, outside, ptrT, rest⟩
  rw [val32_append, show d + 4 * (2 * w) = d + 8 * w by omega, high, zero,
    Nat.mul_zero, Nat.add_zero, low]

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_padModulus_ok (s : State) {base : BitVec 32} {size len w d : Nat}
    (h : CrtPadInput base size len w d s) (operand : Fin 8 := 0) :
    WP isa (padModulus operand) s fun t =>
      val32 t.mem (State.addr base) d (4 * w + 2) = numAt s.mem (State.addr base) w operand.val ∧
      Outside (State.addr base) d (4 * (4 * w + 2)) s.mem t.mem ∧
      t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  have nowrap := h.workspace.nowrap
  have separate := h.separate
  have fits := h.fits
  have small := h.layout.size
  rw [padModulus, WP.seq_iff]
  refine WP.mono (crt_padClear_ready s h) ?_
  rintro u ⟨hu, zeroU, outsideU, restU⟩
  have eq := WorkspaceEq.of_outside (by omega_using [nowrap, separate, fits] : 8 * len < 2 ^ 64) separate outsideU
  have arrFit : arrAt w 8 ≤ 8 * len := h.layout.width ▸ h.layout.layout.2.2.1
  have numberU := eq.number arrFit operand.isLt
  rw [WP.seq_iff]
  refine WP.mono (crt_padModulusArgs_ok u hu.workspace (by omega_using [separate, fits, small]) hu.ptr hu.link operand) ?_
  rintro v ⟨outV, indexV, memV, restV⟩
  have write : InRegions v.wr (off (State.addr base) d) (8 * w) := by
    rw [restV.wr]
    exact ⟨_, hu.workspace.writable, Offset.contains_base _ (by omega_using [fits]) (by omega_using [nowrap, fits])⟩
  have sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨off (State.addr base) d, 8 * w⟩ :=
    Offset.base_disjoint _ separate (by omega_using [nowrap, fits])
  refine WP.mono (exportPadded_ok v (hu.main.congr restV.wr)
    (by rw [memV]; exact hu.layout.layout) (w := w) (by rw [memV]; exact hu.layout.width)
    operand.isLt (k := 2 * w + 2) (by omega_using [nowrap, fits]) write sep (by rw [memV]; exact zeroU)
    ((restV.gpr .r0 (by decide)).trans hu.ptr) indexV outV) ?_
  rintro t ⟨value, outside, ptrT, restT⟩
  rw [memV, numberU] at value
  rw [memV] at outside
  exact ⟨by simpa only [show 2 * w + (2 * w + 2) = 4 * w + 2 by omega_using []] using value,
    outsideU.trans (outside.mono (Nat.le_refl _) (by omega_using [])), ptrT,
    restU.trans ((restV.mono (by decide)).trans restT)⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtFactorProduct`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.WideProductBody`, which this module and modules that import it used -/

section

/-! # The product loop maintains its exact prefix product and public counters -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/WideProductMemory.lean`, which only this module imported.
section

/-! # Product-loop controls change only their dedicated header slots -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem wideProductNext_memory {m m' : Mem} {base : Addr} {ap op : BitVec 32} {c : Nat}
    (mem : m' = ((m.writeW (off base 128) (ap + 4)).writeW
      (off base 136) (op + 4)).writeW (off base 140) (BitVec.ofNat 32 (c - 1))) :
    Outside base 128 16 m m' ∧
      m'.readW (off base 128) 32 = ap + 4 ∧
      m'.readW (off base 136) 32 = op + 4 ∧
      m'.readW (off base 140) 32 = BitVec.ofNat 32 (c - 1) ∧
      m'.readW (off base 132) 32 = m.readW (off base 132) 32 ∧
      m'.readW (off base 144) 32 = m.readW (off base 144) 32 := by
  have a := writeW32_outside m base (d := 128) (ap + 4) (by decide)
  have b := writeW32_outside (m.writeW (off base 128) (ap + 4)) base (d := 136) (op + 4) (by decide)
  have c' := writeW32_outside ((m.writeW (off base 128) (ap + 4)).writeW (off base 136) (op + 4))
    base (d := 140) (BitVec.ofNat 32 (c - 1)) (by decide)
  have outside : Outside base 128 16 m m' := by
    rw [mem]
    exact (a.mono (by decide) (by decide)).trans
      ((b.mono (by decide) (by decide)).trans (c'.mono (by decide) (by decide)))
  refine ⟨outside, ?_, ?_, ?_, ?_, outside_read32 outside (by decide) (by decide)⟩
  · rw [mem, outside_read32 c' (d := 128) (by decide) (by decide),
      outside_read32 b (d := 128) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [mem, outside_read32 c' (d := 136) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [mem, Mem.readW_writeW_self32]
  · rw [mem, outside_read32 c' (d := 132) (by decide) (by decide),
      outside_read32 b (d := 132) (by decide) (by decide),
      outside_read32 a (d := 132) (by decide) (by decide)]

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/HeaderIncrement.lean`, which only this module imported.
section

/-! # Increment a fixed-offset workspace pointer or counter -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str op2_imm dpVal)

theorem headerIncrement_ok (s : State) {base : BitVec 32} {size d k : Nat} {value : BitVec 32}
    (ws : Workspace s base size) (fits : d + 4 ≤ size) (hd : d < 4096) (hk : encodable k = true)
    (ptr : s.gpr .r0 = base) (word : s.mem.readW (off (State.addr base) d) 32 = value) :
    WP isa (.block (headerIncrement d k)) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) d) (value + BitVec.ofNat 32 k) ∧ Rest [.r1] s t := by
  have address : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by have := ws.nowrap; omega)
  unfold headerIncrement
  refine wp_ldr (a := off (State.addr base) d) hd address (ws.read fits) fun u h => ?_
  refine wp_dp (op2_imm hk) fun v j => ?_
  refine wp_str (a := off (State.addr base) d) hd
    (by rw [j.other .r0 (by decide), h.other .r0 (by decide)]; exact address)
    (by rw [j.wr, h.wr]; exact ws.write fits) fun t l => WP.block_nil ?_
  refine ⟨?_, (h.rest (by simp)).trans ((j.rest (by simp)).trans (l.rest _))⟩
  rw [l.mem, j.mem, h.mem, j.gpr, dpVal, h.gpr, word, BitVec.natCast_eq_ofNat]

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/HeaderDecrement.lean`, which only this module imported.
section

/-! # Decrement a fixed-offset public loop counter -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str wp_subs op2_reg op2_imm dpVal ofNat_beq_zero)

theorem headerDecrement_ok (s : State) {base : BitVec 32} {size c d : Nat}
    (ws : Workspace s base size) (fits : d + 4 ≤ size) (hd : d < 4096) (ptr : s.gpr .r0 = base)
    (hc : 0 < c) (hc' : c < 2 ^ 32)
    (count : s.mem.readW (off (State.addr base) d) 32 = BitVec.ofNat 32 c) :
    WP isa (.block (headerDecrement d)) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) d) (BitVec.ofNat 32 (c - 1)) ∧
      t.z = decide (c = 1) ∧ Rest [.r1] s t := by
  have nowrap := ws.nowrap
  have addr : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by omega)
  unfold headerDecrement
  refine wp_ldr (a := off (State.addr base) d) hd addr (ws.read (by omega)) fun s1 u1 => ?_
  refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
  refine wp_str_z (a := off (State.addr base) d) hd
    (by rw [u2.other .r0 (by decide), u1.other .r0 (by decide)]; exact addr)
    (by rw [u2.wr, u1.wr]; exact ws.write (by omega)) fun t u3 z3 => WP.block_nil ?_
  have value : s2.gpr .r1 = BitVec.ofNat 32 (c - 1) := by
    rw [u2.gpr, u1.gpr, count]
    change BitVec.ofNat 32 c - BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
  refine ⟨?_, ?_, (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest _))⟩
  · rw [u3.mem, u2.mem, u1.mem, value]
  · rw [z3, z2, ← u2.gpr, value, ofNat_beq_zero (by omega)]
    simp only [show c - 1 = 0 ↔ c = 1 by omega]


end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/WideProductNext.lean`, which only this module imported.
section

/-! # Advance both product pointers and the public row count -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem wideProductNext_ok (s : State) {base ap op : BitVec 32} {size c : Nat}
    (ws : Workspace s base size) (fit : 148 ≤ size) (ptr : s.gpr .r0 = base)
    (hc : 0 < c) (hc' : c < 2 ^ 32)
    (aPtr : s.mem.readW (off (State.addr base) 128) 32 = ap)
    (oPtr : s.mem.readW (off (State.addr base) 136) 32 = op)
    (count : s.mem.readW (off (State.addr base) 140) 32 = BitVec.ofNat 32 c) :
    WP isa wideProductNext s fun t =>
      t.mem = ((s.mem.writeW (off (State.addr base) 128) (ap + 4)).writeW
        (off (State.addr base) 136) (op + 4)).writeW (off (State.addr base) 140) (BitVec.ofNat 32 (c - 1)) ∧
      t.z = decide (c = 1) ∧ Rest [.r1] s t := by
  rw [wideProductNext, WP.seq_iff]
  refine WP.mono (headerIncrement_ok s ws (by omega) (by decide) (by decide) ptr aPtr) ?_
  rintro u ⟨memU, restU⟩
  have outsideU : Outside (State.addr base) 128 4 s.mem u.mem := by
    rw [memU]; exact writeW32_outside s.mem (State.addr base) (d := 128) (ap + 4) (by decide)
  have oPtrU := (outside_read32 outsideU (d := 136) (by decide) (by decide)).trans oPtr
  have countU := (outside_read32 outsideU (d := 140) (by decide) (by decide)).trans count
  rw [WP.seq_iff]
  refine WP.mono (headerIncrement_ok u (ws.congr restU.wr) (by omega) (by decide) (by decide)
    ((restU.gpr .r0 (by simp)).trans ptr) oPtrU) ?_
  rintro v ⟨memV, restV⟩
  have outsideV : Outside (State.addr base) 136 4 u.mem v.mem := by
    rw [memV]; exact writeW32_outside u.mem (State.addr base) (d := 136) (op + 4) (by decide)
  have countV := (outside_read32 outsideV (d := 140) (by decide) (by decide)).trans countU
  refine WP.mono (headerDecrement_ok v (ws.congr (restV.wr.trans restU.wr)) (by omega) (by decide)
    ((restV.gpr .r0 (by simp)).trans ((restU.gpr .r0 (by simp)).trans ptr)) hc hc' countV) ?_
  rintro t ⟨memT, zero, restT⟩
  exact ⟨by rw [memT, memV, memU]; rfl, zero, restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem wideProductBody_ok (s : State) {s0 : State} {base : BitVec 32} {size o a b m n i : Nat}
    (ctx : WideProductCtx s0 base size o a b m n) (h : WideProductInv s0 base o a b m n i s) (hi : i < m) :
    WP isa wideProductBody s fun t => WideProductInv s0 base o a b m n (i + 1) t ∧
      t.z = decide (i + 1 = m) := by
  have nowrap := ctx.workspace.nowrap
  have outFits := ctx.outFits
  have oHeader := ctx.oHeader
  have aFits := ctx.aFits
  rw [wideProductBody, WP.seq_iff]
  refine WP.mono (wideProductRow_ok s ctx h hi) ?_
  rintro u ⟨value, outside, ptr, rest⟩
  have header (d : Nat) (hd : d + 4 ≤ 148) :
      u.mem.readW (off (State.addr base) d) 32 = s.mem.readW (off (State.addr base) d) 32 :=
    outside_read32 outside (by omega_using [oHeader, hd]) (by omega_using [hd])
  have outsideRow : Outs (State.addr base) [(128, 16), (o, 4 * (m + n + 2))] s.mem u.mem :=
    Outs.of_outside (outside.mono (o' := o) (n' := 4 * (m + n + 2)) (by omega_using []) (by omega_using [hi])) (by simp)
  have restU := h.rest.trans rest
  refine WP.mono (wideProductNext_ok u (ctx.workspace.congr restU.wr) ctx.headerFit ptr
    (by omega_using [hi]) (by omega_using [nowrap, outFits]) ((header 128 (by decide)).trans h.aPtr)
    ((header 136 (by decide)).trans h.oPtr) ((header 140 (by decide)).trans h.count)) ?_
  rintro t ⟨mem, zero, restT⟩
  obtain ⟨outsideT, aPtr, oPtr, count, bPtr, width⟩ := wideProductNext_memory mem
  have outsideAll := h.outside.trans (outsideRow.trans (Outs.of_outside outsideT (by simp)))
  refine ⟨⟨by omega_using [hi], (restT.gpr .r0 (by decide)).trans ptr, ?_, ?_, ?_, ?_, ?_, outsideAll, ?_,
    restU.trans (restT.mono (by decide))⟩, ?_⟩
  · rw [aPtr]
    change base + BitVec.ofNat 32 (a + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · exact bPtr.trans ((header 132 (by decide)).trans h.bPtr)
  · rw [oPtr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [count]; congr 1
  · exact width.trans ((header 144 (by decide)).trans h.width)
  · rw [outsideT.val32 (d := o) (k := m + n + 2) (by omega_using [oHeader]) (by omega_using [nowrap, outFits])]
    exact value
  · rw [zero]; exact decide_eq_decide.mpr (by omega_using [])

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtProductStart`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.CrtCopyHeaderPointer`, which this module and modules that import it used -/

section

/-! # Copy a public buffer pointer between header slots -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str)

theorem crt_copyHeaderPointer_ok (s : State) {base value : BitVec 32} {size src dst : Nat}
    (ws : Workspace s base size) (srcFit : src + 4 ≤ size) (dstFit : dst + 4 ≤ size)
    (hs : src < 4096) (hd : dst < 4096) (ptr : s.gpr .r0 = base)
    (source : s.mem.readW (off (State.addr base) src) 32 = value) :
    WP isa (.block (copyHeaderPointer src dst)) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) dst) value ∧ Rest [.r1] s t := by
  unfold copyHeaderPointer
  refine wp_ldr (a := off (State.addr base) src) hs
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega_using [srcFit, this])) (ws.read srcFit) fun u a => ?_
  refine wp_str (a := off (State.addr base) dst) hd
    (by rw [a.other .r0 (by decide), ptr]; exact addr_add (by have := ws.nowrap; omega_using [dstFit, this]))
    (by rw [a.wr]; exact ws.write dstFit) fun t b => WP.block_nil ?_
  exact ⟨by rw [b.mem, a.mem, a.gpr, source], (a.rest (by simp)).trans (b.rest _)⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtCopyChildPointer`, which this module and modules that import it used -/

section

/-! # Copy a factor's modulus pointer into the multiplication header -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str)

theorem crt_copyChildPointer_ok (s : State) {base value : BitVec 32} {size src dst child slot : Nat}
    (ws : Workspace s base size) (srcFit : src + 4 ≤ size) (dstFit : dst + 4 ≤ size)
    (hs : src < 4096) (hd : dst < 4096) (hslot : slot < 4096) (childFit : child + slot + 4 ≤ size) (ptr : s.gpr .r0 = base)
    (childPtr : s.mem.readW (off (State.addr base) src) 32 = base + BitVec.ofNat 32 child)
    (arrayPtr : s.mem.readW (off (State.addr base) (child + slot)) 32 = value) :
    WP isa (.block (copyChildPointer src dst slot)) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) dst) value ∧ Rest [.r1] s t := by
  unfold copyChildPointer
  refine wp_ldr (a := off (State.addr base) src) hs
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega_using [srcFit, this])) (ws.read srcFit) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) (child + slot)) hslot
    (by rw [a.gpr, childPtr, Offset.add_add]; exact addr_add (by have := ws.nowrap; omega_using [childFit, this]))
    (by rw [a.rd, a.wr]; exact ws.read childFit) fun v b => ?_
  refine wp_str (a := off (State.addr base) dst) hd
    (by rw [b.other .r0 (by decide), a.other .r0 (by decide), ptr]; exact addr_add (by have := ws.nowrap; omega_using [dstFit, this]))
    (by rw [b.wr, a.wr]; exact ws.write dstFit) fun t c => WP.block_nil ?_
  refine ⟨?_, (a.rest (by simp)).trans ((b.rest (by simp)).trans (c.rest _))⟩
  rw [c.mem, b.mem, a.mem, b.gpr, a.mem, arrayPtr]

end VG.Proof.Bignum.Arm

end

end

/-! # Product arguments establish the full schoolbook-loop invariant -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtProductCount.lean`, which only this module imported.
section

/-! # Two native words represent each shared 64-bit RSA limb -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str op2_reg dpVal)

theorem crt_productCount_ok (s : State) {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : 148 ≤ size) (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    WP isa (.block productCount) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr base) 140) (BitVec.ofNat 32 (2 * w))).writeW
        (off (State.addr base) 144) (BitVec.ofNat 32 (2 * w)) ∧ Rest [.r1] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ size) : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by have := ws.nowrap; omega)
  unfold productCount
  refine wp_ldr (a := off (State.addr base) 48) (by decide) (addr 48 (by omega)) (ws.read (by omega)) fun u a => ?_
  refine wp_dp (op2_reg _ _) fun v b => ?_
  have doubled : v.gpr .r1 = BitVec.ofNat 32 (2 * w) := by
    rw [b.gpr, dpVal, a.gpr, count, ← BitVec.ofNat_add, show w + w = 2 * w by omega]
  refine wp_str (a := off (State.addr base) 140) (by decide)
    (by rw [b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 140 (by omega))
    (by rw [b.wr, a.wr]; exact ws.write (by omega)) fun z c => ?_
  have restC : Rest [] v z := c.rest []
  refine wp_str (a := off (State.addr base) 144) (by decide)
    (by rw [restC.gpr .r0 (by simp), b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 144 (by omega))
    (by rw [restC.wr, b.wr, a.wr]; exact ws.write (by omega)) fun t d => WP.block_nil ?_
  refine ⟨?_, (a.rest (by simp)).trans ((b.rest (by simp)).trans ((restC.mono (by simp)).trans (d.rest _)))⟩
  rw [d.mem, restC.gpr .r1 (by simp), c.mem, doubled, b.mem, a.mem]

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtProductMemory.lean`, which only this module imported.
section

/-! # Exact header writes for the factor-product loop controls -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

def crtProductMem (m : Mem) (base : Addr) (p q prod cmp pad : BitVec 32) : Mem :=
  ((((m.writeW (off base 128) p).writeW (off base 132) q).writeW (off base 136) prod).writeW
    (off base 140) cmp).writeW (off base 144) pad

theorem crtProductMem_ok (m : Mem) (base : Addr) (p q prod cmp pad : BitVec 32) :
    let m' := crtProductMem m base p q prod cmp pad
    m'.readW (off base 128) 32 = p ∧ m'.readW (off base 132) 32 = q ∧
    m'.readW (off base 136) 32 = prod ∧ m'.readW (off base 140) 32 = cmp ∧
    m'.readW (off base 144) 32 = pad ∧ Outside base 128 20 m m' := by
  let m1 := m.writeW (off base 128) p
  let m2 := m1.writeW (off base 132) q
  let m3 := m2.writeW (off base 136) prod
  let m4 := m3.writeW (off base 140) cmp
  have a := writeW32_outside m base (d := 128) p (by decide)
  have b := writeW32_outside m1 base (d := 132) q (by decide)
  have c := writeW32_outside m2 base (d := 136) prod (by decide)
  have d := writeW32_outside m3 base (d := 140) cmp (by decide)
  have e := writeW32_outside m4 base (d := 144) pad (by decide)
  change (m4.writeW (off base 144) pad).readW (off base 128) 32 = p ∧ _
  refine ⟨?_, ?_, ?_, ?_, Mem.readW_writeW_self32 _ _ _, ?_⟩
  · rw [outside_read32 e (d := 128) (by decide) (by decide),
      outside_read32 d (d := 128) (by decide) (by decide),
      outside_read32 c (d := 128) (by decide) (by decide),
      outside_read32 b (d := 128) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 144) pad).readW (off base 132) 32 = _
    rw [outside_read32 e (d := 132) (by decide) (by decide),
      outside_read32 d (d := 132) (by decide) (by decide),
      outside_read32 c (d := 132) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 144) pad).readW (off base 136) 32 = _
    rw [outside_read32 e (d := 136) (by decide) (by decide), outside_read32 d (d := 136) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 144) pad).readW (off base 140) 32 = _
    rw [outside_read32 e (d := 140) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · exact (a.mono (by decide) (by decide)).trans ((b.mono (by decide) (by decide)).trans
      ((c.mono (by decide) (by decide)).trans ((d.mono (by decide) (by decide)).trans (e.mono (by decide) (by decide)))))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtProductArgs.lean`, which only this module imported.
section

/-! # Prepare the verified full-width factor multiplication -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- `count` sets the product's counts, `m` rows of `n` words (header words 140
and 144), from any state with `r0 = base` that keeps `s`'s memory outside the
workspace and its word 48, and its stack pointer and permissions. -/
@[expose] public def CountFrom (count : List Instr) (base : BitVec 32) (size m n : Nat) (s : State) : Prop :=
  ∀ z : State, Workspace z base size → z.gpr .r0 = base → z.sp = s.sp → z.rd = s.rd → z.wr = s.wr →
    Frame [⟨State.addr base, size⟩] s.mem z.mem →
    z.mem.readW (off (State.addr base) 48) 32 = s.mem.readW (off (State.addr base) 48) 32 →
    WP isa (.block count) z fun t =>
      t.mem = (z.mem.writeW (off (State.addr base) 140) (BitVec.ofNat 32 m)).writeW
        (off (State.addr base) 144) (BitVec.ofNat 32 n) ∧ Rest [.r1] z t

public theorem CountFrom.after {count : List Instr} {base : BitVec 32} {size m n : Nat} {s u : State}
    (h : CountFrom count base size m n s) (sp : u.sp = s.sp) (rd : u.rd = s.rd) (wr : u.wr = s.wr)
    (F : Frame [⟨State.addr base, size⟩] s.mem u.mem)
    (w48 : u.mem.readW (off (State.addr base) 48) 32 = s.mem.readW (off (State.addr base) 48) 32) :
    CountFrom count base size m n u :=
  fun z ws ptr zsp zrd zwr zF z48 =>
    h z ws ptr (zsp.trans sp) (zrd.trans rd) (zwr.trans wr) (F.trans zF) (z48.trans w48)

/-- `productCount`: the modulus's `2 w` words, both counts. -/
public theorem countFrom_productCount {s : State} {base : BitVec 32} {size w : Nat} (fit : 148 ≤ size)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    CountFrom productCount base size (2 * w) (2 * w) s :=
  fun z ws ptr _ _ _ _ z48 => crt_productCount_ok z ws fit ptr (z48.trans count)

theorem crt_productArgsWith_ok (s : State) {base p q out : BitVec 32} {size cp cq m n : Nat} {coefficient : Bool}
    {count : List Instr} (ws : Workspace s base size) (fit : 236 ≤ size) (hq : 256 ≤ cq)
    (pFit : cp + productOperandSlot coefficient + 4 ≤ size) (qFit : cq + 68 ≤ size) (ptr : s.gpr .r0 = base)
    (pLink : s.mem.readW (off (State.addr base) 224) 32 = base + BitVec.ofNat 32 cp)
    (qLink : s.mem.readW (off (State.addr base) 228) 32 = base + BitVec.ofNat 32 cq)
    (pArray : s.mem.readW (off (State.addr base) (cp + productOperandSlot coefficient)) 32 = p)
    (qArray : s.mem.readW (off (State.addr base) (cq + 64)) 32 = q)
    (product : s.mem.readW (off (State.addr base) 232) 32 = out)
    (hc : CountFrom count base size m n s) :
    WP isa (productArgsWith coefficient count) s fun t =>
      t.mem = crtProductMem s.mem (State.addr base) p q out (BitVec.ofNat 32 m) (BitVec.ofNat 32 n) ∧
      Rest [.r1] s t := by
  rw [productArgsWith, WP.seq_iff]
  refine WP.mono (crt_copyChildPointer_ok s ws (by omega : 224 + 4 ≤ size) (by omega : 128 + 4 ≤ size)
    (by decide) (by decide) (by cases coefficient <;> decide) pFit ptr pLink pArray) ?_
  rintro u ⟨memU, restU⟩
  have outsideU := writeW32_outside s.mem (State.addr base) (d := 128) p (by decide)
  rw [← memU] at outsideU
  rw [WP.seq_iff]
  refine WP.mono (crt_copyChildPointer_ok (value := q) u (ws.congr restU.wr) (by omega : 228 + 4 ≤ size) (by omega : 132 + 4 ≤ size)
    (by decide) (by decide) (by decide) qFit ((restU.gpr .r0 (by simp)).trans ptr)
    (by rw [outside_read32 outsideU (d := 228) (by decide) (by decide)]; exact qLink)
    (by rw [outside_read32 outsideU (d := cq + 64) (by omega) (by have := ws.nowrap; omega)]; exact qArray)) ?_
  rintro v ⟨memV, restV⟩
  have outsideV := writeW32_outside u.mem (State.addr base) (d := 132) q (by decide)
  rw [← memV] at outsideV
  have restSV := restU.trans restV
  rw [WP.seq_iff]
  refine WP.mono (crt_copyHeaderPointer_ok (value := out) v (ws.congr restSV.wr) (by omega : 232 + 4 ≤ size) (by omega : 136 + 4 ≤ size)
    (by decide) (by decide) ((restSV.gpr .r0 (by simp)).trans ptr)
    (by rw [outside_read32 outsideV (d := 232) (by decide) (by decide),
            outside_read32 outsideU (d := 232) (by decide) (by decide)]; exact product)) ?_
  rintro z ⟨memZ, restZ⟩
  have outsideZ := writeW32_outside v.mem (State.addr base) (d := 136) out (by decide)
  rw [← memZ] at outsideZ
  have restSZ := restSV.trans restZ
  have frameZ : Frame [⟨State.addr base, size⟩] s.mem z.mem :=
    (outside_workspace outsideU (by omega)).trans ((outside_workspace outsideV (by omega)).trans
      (outside_workspace outsideZ (by omega)))
  refine WP.mono (hc z (ws.congr restSZ.wr) ((restSZ.gpr .r0 (by simp)).trans ptr) restSZ.sp restSZ.rd restSZ.wr
    frameZ (by rw [outside_read32 outsideZ (d := 48) (by decide) (by decide),
            outside_read32 outsideV (d := 48) (by decide) (by decide),
            outside_read32 outsideU (d := 48) (by decide) (by decide)])) ?_
  rintro t ⟨memT, restT⟩
  refine ⟨?_, restSZ.trans restT⟩
  rw [memT, memZ, memV, memU]
  rfl

theorem crt_productArgs_ok (s : State) {base p q out : BitVec 32} {size cp cq w : Nat} {coefficient : Bool}
    (ws : Workspace s base size) (fit : 236 ≤ size) (hq : 256 ≤ cq)
    (pFit : cp + productOperandSlot coefficient + 4 ≤ size) (qFit : cq + 68 ≤ size) (ptr : s.gpr .r0 = base)
    (pLink : s.mem.readW (off (State.addr base) 224) 32 = base + BitVec.ofNat 32 cp)
    (qLink : s.mem.readW (off (State.addr base) 228) 32 = base + BitVec.ofNat 32 cq)
    (pArray : s.mem.readW (off (State.addr base) (cp + productOperandSlot coefficient)) 32 = p)
    (qArray : s.mem.readW (off (State.addr base) (cq + 64)) 32 = q)
    (product : s.mem.readW (off (State.addr base) 232) 32 = out)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    WP isa (productArgs coefficient) s fun t =>
      t.mem = crtProductMem s.mem (State.addr base) p q out (BitVec.ofNat 32 (2 * w)) (BitVec.ofNat 32 (2 * w)) ∧
      Rest [.r1] s t :=
  crt_productArgsWith_ok s ws fit hq pFit qFit ptr pLink qLink pArray qArray product
    (countFrom_productCount (by omega) count)

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtProductStart (base : BitVec 32) (size o a b m n : Nat) (s : State) : Prop where
  context : WideProductCtx s base size o a b m n
  initial : WideProductInv s base o a b m n 0 s

/-- The context of a product of fewer words. -/
theorem WideProductCtx.narrow {s : State} {base : BitVec 32} {size o a b M N m n : Nat}
    (h : WideProductCtx s base size o a b M N) (hm : 0 < m) (hm' : m ≤ M) (hn : 0 < n) (hn' : n ≤ N) :
    WideProductCtx s base size o a b m n :=
  ⟨h.workspace, hm, hn, h.headerFit, h.aHeader, h.bHeader, h.oHeader, by have := h.aFits; omega_using [hm', this],
    by have := h.bFits; omega_using [hn', this], by have := h.outFits; omega_using [hm', hn', this], by have := h.separateA; omega_using [hm', hn', this],
    by have := h.separateB; omega_using [hm', hn', this], h.stackRead, h.stackSep, h.saved⟩

theorem crt_productArgsWith_ready (s : State) {base : BitVec 32} {size o a b cp cq w m n : Nat} {coefficient : Bool}
    {count : List Instr} (h : CrtProductInput base size o a b cp cq w s coefficient)
    (hc : CountFrom count base size m n s) (hm : 0 < m) (hm' : m ≤ 2 * w) (hn : 0 < n) (hn' : n ≤ 2 * w)
    (zero : val32 s.mem (State.addr base) o (m + n + 2) = 0) :
    WP isa (productArgsWith coefficient count) s fun t => CrtProductStart base size o a b m n t ∧
      Outside (State.addr base) 128 20 s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest [.r1] s t := by
  have outFit := h.outFits
  have beforeP := h.pBeforeOut
  have beforeQ := h.qBeforeOut
  refine WP.mono (crt_productArgsWith_ok s h.workspace h.parentFit h.qHeader (by omega_using [outFit, beforeP]) (by omega_using [outFit, beforeQ])
    h.ptr h.pLink h.qLink h.pArray h.qArray h.product hc) ?_
  rintro t ⟨memT, rest⟩
  have result := crtProductMem_ok s.mem (State.addr base)
    (base + BitVec.ofNat 32 a) (base + BitVec.ofNat 32 b) (base + BitVec.ofNat 32 o)
    (BitVec.ofNat 32 m) (BitVec.ofNat 32 n)
  dsimp only at result
  rw [← memT] at result
  obtain ⟨p, q, out, count, width, outside⟩ := result
  have frame := outside_workspace outside (size := size) h.headerFit
  have ctx := (h.toWideProductCtx.narrow hm hm' hn hn').after_frame rest frame
  have zeroT : val32 t.mem (State.addr base) o (m + n + 2) = 0 := by
    rw [outside.val32 (by have := h.oHeader; omega_using [this]) (by have := h.workspace.nowrap; omega_using [hm', hn', outFit, this]), zero]
  refine ⟨⟨ctx, ?_⟩, outside, frame, rest⟩
  refine ⟨by omega_using [], (rest.gpr .r0 (by simp)).trans h.ptr, ?_, q, ?_, ?_, width,
    Outs.refl _ _ _, ?_, Rest.refl _ _⟩
  · simpa only [Nat.mul_zero, Nat.add_zero] using p
  · simpa only [Nat.mul_zero, Nat.add_zero] using out
  · simpa only [Nat.sub_zero] using count
  · simp only [val32, Nat.zero_mul]; exact zeroT

theorem crt_productArgs_ready (s : State) {base : BitVec 32} {size o a b cp cq w : Nat} {coefficient : Bool}
    (h : CrtProductInput base size o a b cp cq w s coefficient)
    (zero : val32 s.mem (State.addr base) o (2 * w + 2 * w + 2) = 0) :
    WP isa (productArgs coefficient) s fun t => CrtProductStart base size o a b (2 * w) (2 * w) t ∧
      Outside (State.addr base) 128 20 s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest [.r1] s t :=
  crt_productArgsWith_ready s h (countFrom_productCount h.headerFit h.count) h.positiveA (Nat.le_refl _)
    h.positiveB (Nat.le_refl _) zero

end VG.Proof.Bignum.Arm

end

end

/-! # Exact factor multiplication, including buffer initialization -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/WideProduct.lean`, which only this module imported.
section

/-! # Exact wide multiplication terminates after the public number of source words -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem wideProduct_ok (s : State) {base : BitVec 32} {size o a b m n : Nat}
    (ctx : WideProductCtx s base size o a b m n)
    (ptr : s.gpr .r0 = base)
    (aPtr : s.mem.readW (off (State.addr base) 128) 32 = base + BitVec.ofNat 32 a)
    (bPtr : s.mem.readW (off (State.addr base) 132) 32 = base + BitVec.ofNat 32 b)
    (oPtr : s.mem.readW (off (State.addr base) 136) 32 = base + BitVec.ofNat 32 o)
    (count : s.mem.readW (off (State.addr base) 140) 32 = BitVec.ofNat 32 m)
    (width : s.mem.readW (off (State.addr base) 144) 32 = BitVec.ofNat 32 n)
    (zero : val32 s.mem (State.addr base) o (m + n + 2) = 0) :
    WP isa wideProduct s fun t =>
      val32 t.mem (State.addr base) o (m + n + 2) =
        val32 s.mem (State.addr base) a m * val32 s.mem (State.addr base) b n ∧
      Outs (State.addr base) [(128, 16), (o, 4 * (m + n + 2))] s.mem t.mem ∧
      t.gpr .r0 = base ∧ Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => ∃ i, i + k = m ∧ 0 < k ∧ WideProductInv s base o a b m n i t
  unfold wideProduct
  refine WP.loop (M := isa) I ?_ m s ?_
  · intro k t inv
    obtain ⟨i, ik, hk, hi⟩ := inv
    refine WP.mono (wideProductBody_ok t ctx hi (by omega)) ?_
    rintro u ⟨next, zero⟩
    by_cases last : i + 1 = m
    · left
      refine ⟨?_, ?_, next.outside, next.ptr, ctx.frame next.outside, next.rest⟩
      · change some (!u.z) = some false
        simp only [zero, last, decide_true, Bool.not_true]
      · simpa only [last] using next.value
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, next⟩
      change some (!u.z) = some true
      simp only [zero, last, decide_false, Bool.not_false]
  · refine ⟨0, by omega, ctx.positiveA, ?_⟩
    refine ⟨by omega, ptr, ?_, bPtr, ?_, ?_, width, Outs.refl _ _ _, ?_, Rest.refl _ _⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using aPtr
    · simpa only [Nat.mul_zero, Nat.add_zero] using oPtr
    · simpa only [Nat.sub_zero] using count
    · simp only [val32, Nat.zero_mul]; exact zero

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- The first `k` of `n` zero words. -/
theorem val32_zero_prefix {mem : Mem} {B : Addr} {d n k : Nat} (h : val32 mem B d n = 0) (hk : k ≤ n) :
    val32 mem B d k = 0 := by
  have a := val32_append mem B d k (n - k)
  rw [show k + (n - k) = n by omega_using [hk], h] at a
  omega_using [a]

/-- The product of the first `m` words of `a` and `n` of `b`, its output of
`4 w + 2` words cleared first, by `count`'s counts. -/
theorem crt_factorProductWith_ok (s : State) {base : BitVec 32} {size o a b cp cq w m n : Nat} {coefficient : Bool}
    {count : List Instr} (h : CrtProductInput base size o a b cp cq w s coefficient)
    (hc : CountFrom count base size m n s) (hm : 0 < m) (hm' : m ≤ 2 * w) (hn : 0 < n) (hn' : n ≤ 2 * w) :
    WP isa (factorProductWith coefficient count) s fun t =>
      val32 t.mem (State.addr base) o (2 * w + 2 * w + 2) =
        val32 s.mem (State.addr base) a m * val32 s.mem (State.addr base) b n ∧
      Outs (State.addr base) [(128, 20), (o, 4 * (2 * w + 2 * w + 2))] s.mem t.mem ∧
      t.gpr .r0 = base ∧ Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have nowrap := h.workspace.nowrap
  have aFits := h.aFits
  have bFits := h.bFits
  have aHeader := h.aHeader
  have bHeader := h.bHeader
  have outFits := h.outFits
  have sepA := h.separateA
  have sepB := h.separateB
  have oHeader := h.oHeader
  rw [factorProductWith, WP.seq_iff]
  refine WP.mono (crt_productClear_ready s h) ?_
  rintro u ⟨inputU, zeroU, outsideU, frameU, restU⟩
  have aU := outsideU.val32 (d := a) (k := m) (by omega_using [hm', sepA]) (by omega_using [hm', nowrap, aFits])
  have bU := outsideU.val32 (d := b) (k := n) (by omega_using [hn', sepB]) (by omega_using [hn', nowrap, bFits])
  -- The cleared output: its first `m + n + 2` words, and those above them.
  have split := val32_append u.mem (State.addr base) o (m + n + 2) (2 * w + 2 * w + 2 - (m + n + 2))
  rw [show m + n + 2 + (2 * w + 2 * w + 2 - (m + n + 2)) = 2 * w + 2 * w + 2 by omega_using [hm', hn'], zeroU] at split
  have pos := Nat.two_pow_pos (32 * (m + n + 2))
  have zeroLo : val32 u.mem (State.addr base) o (m + n + 2) = 0 := by omega_using [split]
  have zeroHi : val32 u.mem (State.addr base) (o + 4 * (m + n + 2)) (2 * w + 2 * w + 2 - (m + n + 2)) = 0 := by
    rcases Nat.eq_zero_or_pos (val32 u.mem (State.addr base) (o + 4 * (m + n + 2))
      (2 * w + 2 * w + 2 - (m + n + 2))) with z | z
    · exact z
    · have := Nat.le_mul_of_pos_right (2 ^ (32 * (m + n + 2))) z; omega_using [split, pos, this]
  have hcU : CountFrom count base size m n u := hc.after restU.sp restU.rd restU.wr frameU
    (outside_read32 outsideU (d := 48) (by omega_using [oHeader]) (by omega_using []))
  rw [WP.seq_iff]
  refine WP.mono (crt_productArgsWith_ready u inputU hcU hm hm' hn hn' zeroLo) ?_
  rintro v ⟨start, outsideV, frameV, restV⟩
  have aV := outsideV.val32 (d := a) (k := m) (by omega_using [aHeader]) (by omega_using [hm', nowrap, aFits])
  have bV := outsideV.val32 (d := b) (k := n) (by omega_using [bHeader]) (by omega_using [hn', nowrap, bFits])
  have hiV := outsideV.val32 (d := o + 4 * (m + n + 2)) (k := 2 * w + 2 * w + 2 - (m + n + 2)) (by omega_using [oHeader])
    (by omega_using [hm, hm', hn, hn', nowrap, aFits, bFits, aHeader, bHeader, outFits, sepA, sepB, oHeader])
  have initial := start.initial
  have p := initial.aPtr
  have out := initial.oPtr
  have count := initial.count
  have zero := initial.value
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, val32, Nat.zero_mul] at p out count zero
  refine WP.mono (wideProduct_ok v start.context initial.ptr p initial.bPtr out count initial.width zero) ?_
  rintro t ⟨value, outsideT, ptrT, frameT, restT⟩
  rw [aV, bV, aU, bU] at value
  have hiT := outsideT.val32 (d := o + 4 * (m + n + 2)) (k := 2 * w + 2 * w + 2 - (m + n + 2))
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [hm, hm', hn, hn', nowrap, aFits, bFits, aHeader, bHeader, outFits, sepA, sepB, oHeader])
  have widened : Outs (State.addr base) [(128, 20), (o, 4 * (2 * w + 2 * w + 2))] v.mem t.mem := by
    intro x hx
    apply outsideT x
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hfirst := hx (128, 20) (by simp)
      omega_using [hfirst]
    · have hsecond := hx (o, 4 * (2 * w + 2 * w + 2)) (by simp)
      simp only at hsecond ⊢
      omega_using [hm', hn', hsecond]
  refine ⟨?_, (Outs.of_outside outsideU (by simp)).trans ((Outs.of_outside outsideV (by simp)).trans widened),
    ptrT, frameU.trans (frameV.trans frameT), restU.trans ((restV.mono (by decide)).trans restT)⟩
  rw [show 2 * w + 2 * w + 2 = m + n + 2 + (2 * w + 2 * w + 2 - (m + n + 2)) by omega_using [hm', hn'], val32_append, value, hiT,
    hiV, zeroHi, Nat.mul_zero, Nat.add_zero]

theorem crt_factorProduct_ok (s : State) {base : BitVec 32} {size o a b cp cq w : Nat} {coefficient : Bool}
    (h : CrtProductInput base size o a b cp cq w s coefficient) :
    WP isa (factorProduct coefficient) s fun t =>
      val32 t.mem (State.addr base) o (2 * w + 2 * w + 2) =
        val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) ∧
      Outs (State.addr base) [(128, 20), (o, 4 * (2 * w + 2 * w + 2))] s.mem t.mem ∧
      t.gpr .r0 = base ∧ Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t :=
  crt_factorProductWith_ok s h (countFrom_productCount h.headerFit h.count) h.positiveA (Nat.le_refl _)
    h.positiveB (Nat.le_refl _)

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtValidateProduct`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.CrtCheckProductState`, which this module and modules that import it used -/

section

/-! # Product-comparison inputs survive padding the modulus buffer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtCheckProductInput (base : BitVec 32) (size len o a d w : Nat) (s : State) : Prop where
  padding : CrtPadInput base size len w d s
  comparison : CrtCompareInput base size o a d w s
  separate : a + 4 * (4 * w + 2) ≤ d ∨ d + 4 * (4 * w + 2) ≤ a

theorem crt_padComparison_ready (s : State) {base : BitVec 32} {size len o a d w : Nat}
    (h : CrtCheckProductInput base size len o a d w s) :
    WP isa padModulus s fun t => CrtCompareInput base size o a d w t ∧
      val32 t.mem (State.addr base) a (4 * w + 2) = val32 s.mem (State.addr base) a (4 * w + 2) ∧
      val32 t.mem (State.addr base) d (4 * w + 2) = Proof.Rsa.Mont.numAt s.mem (State.addr base) w 0 ∧
      Outside (State.addr base) d (4 * (4 * w + 2)) s.mem t.mem ∧ Rest roundClobbers s t := by
  have small := h.padding.layout.size
  have separate := h.padding.separate
  have nowrap := h.padding.workspace.nowrap
  have aFit := h.comparison.subtraction.aFits
  refine WP.mono (crt_padModulus_ok s h.padding) ?_
  rintro t ⟨value, outside, ptr, rest⟩
  have frame := outside_workspace outside h.padding.fits
  have c := h.comparison
  have ctx : SubCtx t base size o a d (4 * w + 2) :=
    ⟨c.subtraction.nowrap, c.subtraction.outFits, c.subtraction.aFits, c.subtraction.bFits,
      c.subtraction.sepA, c.subtraction.sepB, by rw [rest.wr]; exact c.subtraction.writable⟩
  refine ⟨⟨c.workspace.congr rest.wr, c.fit, ctx, ptr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    outside.val32 h.separate (by omega_using [nowrap, aFit]), value, outside, rest⟩
  · exact (outside_read32 outside (by omega_using [small, separate]) (by decide)).trans c.count
  · exact (outside_read32 outside (by omega_using [small, separate]) (by decide)).trans c.output
  · exact (outside_read32 outside (by omega_using [small, separate]) (by decide)).trans c.first
  · exact (outside_read32 outside (by omega_using [small, separate]) (by decide)).trans c.second
  · rw [rest.rd, rest.wr, rest.sp]; exact c.stackRead
  · rw [rest.sp]; exact c.stackSep
  · exact saved_base_kept frame c.stackSep c.saved rest.sp

end VG.Proof.Bignum.Arm

end

end

/-! # Exact full product validation against the original RSA modulus -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtCheckProduct.lean`, which only this module imported.
section

/-! # Full-width factor validation against the original modulus -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_checkProduct_ok (s : State) {base : BitVec 32} {size len o a d w : Nat}
    (h : CrtCheckProductInput base size len o a d w s) :
    WP isa checkProduct s fun t =>
      t.gpr .r11 = (if val32 s.mem (State.addr base) a (4 * w + 2) =
        Proof.Rsa.Mont.numAt s.mem (State.addr base) w 0 then 1 else 0) ∧
      Outs (State.addr base) [(d, 4 * (4 * w + 2)), (o, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  rw [checkProduct, WP.seq_iff]
  refine WP.mono (crt_padComparison_ready s h) ?_
  rintro u ⟨ready, first, second, outsideU, restU⟩
  refine WP.mono (crt_compareProduct_ok u ready) ?_
  rintro t ⟨value, outsideT, frameT, ptrT, restT⟩
  rw [first, second] at value
  exact ⟨value, (Outs.of_outside outsideU (by simp)).trans (Outs.of_outside outsideT (by simp)),
    (outside_workspace outsideU h.padding.fits).trans frameT, ptrT, restU.trans restT⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtProductValidationState.lean`, which only this module imported.
section

/-! # Factor multiplication preserves the inputs to product validation -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem CrtCheckProductInput.after_product {s t : State} {base : BitVec 32} {size len o a d w : Nat}
    (h : CrtCheckProductInput base size len o a d w s) (sep : 8 * len ≤ a)
    (outside : Outs (State.addr base) [(128, 20), (a, 4 * (4 * w + 2))] s.mem t.mem)
    (frame : Frame [⟨State.addr base, size⟩] s.mem t.mem) (ptr : t.gpr .r0 = base)
    (rest : Rest roundClobbers s t) :
    CrtCheckProductInput base size len o a d w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 := by
  have small := h.padding.layout.size
  have nowrap := h.padding.workspace.nowrap
  have head := control_buffers_header outside (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega)
  have word (j : Nat) (hj : j = 48 ∨ j = 232 ∨ j = 236 ∨ j = 240) :
      t.mem.readW (off (State.addr base) j) 32 = s.mem.readW (off (State.addr base) j) 32 := by
    apply outs_readW outside
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
    · omega
  have saved := saved_base_kept frame h.padding.stackSep h.padding.saved rest.sp
  have pad : CrtPadInput base size len w d t :=
    ⟨h.padding.workspace.congr rest.wr, h.padding.main.congr rest.wr, h.padding.layout.of_header_eq head,
      h.padding.separate, h.padding.fits, ptr, (word 240 (by simp)).trans h.padding.link,
      by rw [rest.rd, rest.wr, rest.sp]; exact h.padding.stackRead,
      by rw [rest.sp]; exact h.padding.stackSep, saved⟩
  have c := h.comparison
  have ctx : SubCtx t base size o a d (4 * w + 2) :=
    ⟨c.subtraction.nowrap, c.subtraction.outFits, c.subtraction.aFits, c.subtraction.bFits,
      c.subtraction.sepA, c.subtraction.sepB, by rw [rest.wr]; exact c.subtraction.writable⟩
  have compare : CrtCompareInput base size o a d w t :=
    ⟨c.workspace.congr rest.wr, c.fit, ctx, ptr, (word 48 (by simp)).trans c.count,
      (word 236 (by simp)).trans c.output, (word 232 (by simp)).trans c.first,
      (word 240 (by simp)).trans c.second,
      by rw [rest.rd, rest.wr, rest.sp]; exact c.stackRead,
      by rw [rest.sp]; exact c.stackSep,
      saved_base_kept frame c.stackSep c.saved rest.sp⟩
  refine ⟨⟨pad, compare, h.separate⟩, ?_⟩
  have fit : arrAt w 8 ≤ 8 * len := h.padding.layout.width ▸ h.padding.layout.layout.2.2.1
  have bound := Nat.le_trans (array_end_le (w := w) (j := 0) (by decide : 0 < 8)) fit
  rw [numAt_native, numAt_native]
  apply outside.val32
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right; simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega
    · left; simp only; omega
  · have := h.padding.main.nowrap; omega

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtValidateInput (base : BitVec 32) (size len product cmp pad a b cp cq w : Nat) (s : State) : Prop where
  multiplication : CrtProductInput base size product a b cp cq w s
  comparison : CrtCheckProductInput base size len cmp product pad w s
  separate : 8 * len ≤ product

theorem crt_validationProductWith_ready (s : State) {base : BitVec 32} {size len product cmp pad a b cp cq w m n : Nat}
    {count : List Instr} (h : CrtValidateInput base size len product cmp pad a b cp cq w s)
    (hc : CountFrom count base size m n s) (hm : 0 < m) (hm' : m ≤ 2 * w) (hn : 0 < n) (hn' : n ≤ 2 * w) :
    WP isa (factorProductWith false count) s fun t => CrtCheckProductInput base size len cmp product pad w t ∧
      val32 t.mem (State.addr base) product (4 * w + 2) =
        val32 s.mem (State.addr base) a m * val32 s.mem (State.addr base) b n ∧
      Proof.Rsa.Mont.numAt t.mem (State.addr base) w 0 = Proof.Rsa.Mont.numAt s.mem (State.addr base) w 0 ∧
      Outs (State.addr base) [(128, 20), (product, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (crt_factorProductWith_ok s h.multiplication hc hm hm' hn hn') ?_
  rintro t ⟨value, outside, ptr, frame, rest⟩
  rw [show 2 * w + 2 * w + 2 = 4 * w + 2 by omega_using []] at value outside
  obtain ⟨ready, modulus⟩ := h.comparison.after_product h.separate outside frame ptr rest
  exact ⟨ready, value, modulus, outside, frame, rest⟩

theorem crt_validationProduct_ready (s : State) {base : BitVec 32} {size len product cmp pad a b cp cq w : Nat}
    (h : CrtValidateInput base size len product cmp pad a b cp cq w s) :
    WP isa factorProduct s fun t => CrtCheckProductInput base size len cmp product pad w t ∧
      val32 t.mem (State.addr base) product (4 * w + 2) =
        val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) ∧
      Proof.Rsa.Mont.numAt t.mem (State.addr base) w 0 = Proof.Rsa.Mont.numAt s.mem (State.addr base) w 0 ∧
      Outs (State.addr base) [(128, 20), (product, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t :=
  crt_validationProductWith_ready s h (countFrom_productCount h.multiplication.headerFit h.multiplication.count)
    h.multiplication.positiveA (Nat.le_refl _) h.multiplication.positiveB (Nat.le_refl _)

theorem crt_validateProductWith_ok (s : State) {base : BitVec 32} {size len product cmp pad a b cp cq w m n : Nat}
    {count : List Instr} (h : CrtValidateInput base size len product cmp pad a b cp cq w s)
    (hc : CountFrom count base size m n s) (hm : 0 < m) (hm' : m ≤ 2 * w) (hn : 0 < n) (hn' : n ≤ 2 * w) :
    WP isa (validateProductWith count) s fun t =>
      t.gpr .r11 = (if val32 s.mem (State.addr base) a m * val32 s.mem (State.addr base) b n =
        Proof.Rsa.Mont.numAt s.mem (State.addr base) w 0 then 1 else 0) ∧
      Outs (State.addr base) [(128, 20), (product, 4 * (4 * w + 2)),
        (pad, 4 * (4 * w + 2)), (cmp, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  rw [validateProductWith, WP.seq_iff]
  refine WP.mono (crt_validationProductWith_ready s h hc hm hm' hn hn') ?_
  rintro u ⟨ready, productU, modulusU, outsideU, frameU, restU⟩
  refine WP.mono (crt_checkProduct_ok u ready) ?_
  rintro t ⟨value, outsideT, frameT, ptrT, restT⟩
  rw [productU, modulusU] at value
  refine ⟨value, ?_, frameU.trans frameT, ptrT, restU.trans restT⟩
  exact (outsideU.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp)).trans (outsideT.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp))

theorem crt_validateProduct_ok (s : State) {base : BitVec 32} {size len product cmp pad a b cp cq w : Nat}
    (h : CrtValidateInput base size len product cmp pad a b cp cq w s) :
    WP isa validateProduct s fun t =>
      t.gpr .r11 = (if val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) =
        Proof.Rsa.Mont.numAt s.mem (State.addr base) w 0 then 1 else 0) ∧
      Outs (State.addr base) [(128, 20), (product, 4 * (4 * w + 2)),
        (pad, 4 * (4 * w + 2)), (cmp, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t :=
  crt_validateProductWith_ok s h (countFrom_productCount h.multiplication.headerFit h.multiplication.count)
    h.multiplication.positiveA (Nat.le_refl _) h.multiplication.positiveB (Nat.le_refl _)

end VG.Proof.Bignum.Arm

end

end

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
  omega_using []

theorem CrtShared.compare_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    CrtCompareInput g.base g.size (compareOffset g.words) (productOffset g.words) (modulusOffset g.words) g.words s := by
  have size := h.buffers.storageFits
  have small : 244 ≤ g.size := by
    have fit := h.buffers.context.main.nowrap
    have size' := h.main.toCrtLayoutState.size
    simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productOffset, stride] at size
    omega_using [size, size']
  refine ⟨h.buffers.workspace, small, ?_, ready.ptr,
    h.main.toCrtLayoutState.nativeCount h.buffers.context.main, h.main.compare, h.main.product,
    h.main.modulus, ready.stackRead, h.stack.separate.sub_left (Region.sub_prefix (by decide)), ready.saved⟩
  refine ⟨h.buffers.workspace.nowrap, ?_, ?_, Nat.le_trans (crt_modulus_end_le _) size, ?_, ?_,
    h.buffers.workspace.writable⟩
  all_goals simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productBytes, productWords] at size ⊢
  · omega_using [size]
  · omega_using [size]
  · right; omega_using []
  · left; omega_using []

theorem CrtShared.validate_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    CrtValidateInput g.base g.size (workspaceWords g.words) (productOffset g.words)
      (compareOffset g.words) (modulusOffset g.words) (crtProductA g.words false) (crtProductB g.words)
      (pOffset g.words) (qOffset g.words) g.words s := by
  refine ⟨h.product_input ready false, ⟨h.pad_input ready, h.compare_input ready, ?_⟩, ?_⟩
  · left
    simp only [modulusOffset, compareOffset, productBytes, productWords]
    omega_using []
  · simp only [productOffset, stride]; omega_using []

end VG.Proof.Bignum.Arm
