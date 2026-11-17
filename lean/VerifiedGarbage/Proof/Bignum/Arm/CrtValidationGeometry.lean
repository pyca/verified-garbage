module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
public import VerifiedGarbage.Impl.Bignum.Arm.CrtValidateProduct
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtFactorProduct
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.CrtCheckProduct
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.ControlBuffers
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulus
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCompareProduct
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusState
public import VerifiedGarbage.Impl.Bignum.Arm.CrtPadModulus

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
