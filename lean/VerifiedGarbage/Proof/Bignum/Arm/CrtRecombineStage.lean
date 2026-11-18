module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.CrtRecombine
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.ControlBuffers
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusArgs
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFinishRecombine
public import VerifiedGarbage.Proof.Bignum.Arm.CrtAddWide
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.CrtQSource
import VerifiedGarbage.Proof.Bignum.Arm.TransferArray
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout

/-! ### `Bignum.Arm.CrtImportFinalResidue`, which this module and modules that import it used -/

section

/-! # Copy the final q residue into the main reconstruction workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem crt_importFinalResidue_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa (.seq (.block CrtFn.qSource) (transferArray 1 6)) s fun t =>
      CrtShared g bs t ∧ LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr g.base) g.words 1 = numAt s.mem (State.addr (crtQ g.base g.words)) g.words 6 ∧
      Frame [⟨State.addr g.base, 8 * workspaceWords g.words⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (crt_qSource_ok s h) ?_
  rintro u ⟨qptr, memU, restU⟩
  have sharedU := h.of_mem memU restU
  have readyU := ready.of_mem memU restU ((restU.gpr .r0 (by decide)).trans ready.ptr)
  have input : TransferArrayInput g.base (crtQ g.base g.words)
      (workspaceWords g.words) (workspaceWords g.words) g.words u :=
    ⟨readyU, sharedU.buffers.context.q, sharedU.q, qptr, h.buffers.context.sepMQ.symm⟩
  refine WP.mono (transferArray_ok u input (by decide : 1 < 8) (by decide : 6 < 8)) ?_
  rintro t ⟨readyT, value, keeps, frame, rest⟩
  have header (d : Nat) (hd : d + 4 ≤ 256) :
      t.mem.readW (off (State.addr g.base) d) 32 = u.mem.readW (off (State.addr g.base) d) 32 :=
    keeps_header_readW keeps sharedU.main.toCrtLayoutState.size hd
  have mainT : CrtMainState g.base (workspaceWords g.words) g.words t.mem :=
    ⟨⟨readyT.layout, readyT.width⟩, (header 224 (by decide)).trans sharedU.main.p,
      (header 228 (by decide)).trans sharedU.main.q, (header 232 (by decide)).trans sharedU.main.product,
      (header 236 (by decide)).trans sharedU.main.compare, (header 240 (by decide)).trans sharedU.main.modulus⟩
  have modulus := keeps_array_num keeps h.buffers.context.arraysFit
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 0) (by decide : 0 ≠ 1)
  have sharedT := sharedU.after_main (frame.mono (by simp)) rest mainT modulus
  rw [memU] at value frame
  exact ⟨sharedT, readyT, value, frame, (restU.mono (by decide)).trans rest⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtRecombineGeometry`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.CrtRecombineProduct`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.CrtFinishRecombine`, which this module and modules that import it used -/

section

/-! # Exact CRT product-plus-residue reconstruction -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtRecombineValue.lean`, which only this module imported.
section

/-! # The padded CRT residue fits the addition loop's input width -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)

theorem val32_prefix_of_eq {m : Mem} {base : Addr} {d n k value : Nat}
    (h : val32 m base d (n + k) = value) (fit : value < 2 ^ (32 * n)) :
    val32 m base d n = value := by
  have eq := congrArg (fun x => x % 2 ^ (32 * n)) h
  rw [val32_append] at eq
  simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
    Nat.add_zero, Nat.mod_eq_of_lt (val32_lt m base d n), Nat.mod_eq_of_lt fit] using eq

theorem crt_paddedResidue_low {m before : Mem} {base : Addr} {d w o : Nat}
    (h : val32 m base d (4 * w + 2) = numAt before base w o) :
    val32 m base d (4 * w) = numAt before base w o := by
  apply val32_prefix_of_eq h
  rw [numAt_native]
  exact Nat.lt_of_lt_of_le (val32_lt before base (arrAt w o) (2 * w))
    (Nat.pow_le_pow_right (by decide) (by omega))

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure CrtFinishInput (base : BitVec 32) (size len w o d : Nat) (s : State) : Prop where
  padding : CrtPadInput base size len w d s
  row : RowCtx s base size o d (4 * w)
  outputFits : o + 4 * (4 * w + 2) ≤ size
  separate : o + 4 * (4 * w + 2) ≤ d
  output : s.mem.readW (off (State.addr base) 232) 32 = base + BitVec.ofNat 32 o
  sumFits : val32 s.mem (State.addr base) o (4 * w + 2) + numAt s.mem (State.addr base) w 1 < 2 ^ (32 * (4 * w + 2))

theorem crt_finishPad_ready (s : State) {base : BitVec 32} {size len w o d : Nat}
    (h : CrtFinishInput base size len w o d s) :
    WP isa (padModulus 1) s fun t => CrtAddWideInput base size o d w t ∧
      val32 t.mem (State.addr base) o (4 * w + 2) = val32 s.mem (State.addr base) o (4 * w + 2) ∧
      val32 t.mem (State.addr base) d (4 * w) = numAt s.mem (State.addr base) w 1 ∧
      Outside (State.addr base) d (4 * (4 * w + 2)) s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have p := h.padding
  have small := p.layout.size
  have nowrap := p.workspace.nowrap
  have sep := p.separate
  have fits := p.fits
  refine WP.mono (crt_padModulus_ok s p 1) ?_
  rintro u ⟨padded, outside, ptrU, restU⟩
  have low := crt_paddedResidue_low padded
  have product := outside.val32 (d := o) (k := 4 * w + 2) (Or.inl h.separate) (by have := h.outputFits; omega_using [nowrap, this])
  have frame := outside_workspace outside p.fits
  have count := p.layout.nativeCount p.main
  have ready : CrtAddWideInput base size o d w u := by
    refine ⟨p.workspace.congr restU.wr, by omega_using [small, sep, fits],
      ⟨h.row.nowrap, h.row.outFits, h.row.inFits, h.row.separate, by rw [restU.wr]; exact h.row.writable⟩,
      ?_, h.outputFits, ptrU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hw := p.layout.width ▸ p.layout.layout.1; omega_using [hw]
    · rw [outside_read32 outside (d := 48) (by omega_using [small, sep]) (by decide)]; exact count
    · rw [outside_read32 outside (d := 232) (by omega_using [small, sep]) (by decide)]; exact h.output
    · rw [outside_read32 outside (d := 240) (by omega_using [small, sep]) (by decide)]; exact p.link
    · rw [product, low]; exact h.sumFits
    · rw [restU.rd, restU.wr, restU.sp]; exact p.stackRead
    · rw [restU.sp]; exact p.stackSep
    · exact saved_base_kept frame p.stackSep p.saved restU.sp
  exact ⟨ready, product, low, outside, frame, restU⟩

theorem crt_finishRecombine_ok (s : State) {base : BitVec 32} {size len w o d : Nat}
    (h : CrtFinishInput base size len w o d s) :
    WP isa finishRecombine s fun t =>
      val32 t.mem (State.addr base) o (4 * w + 2) =
        val32 s.mem (State.addr base) o (4 * w + 2) + numAt s.mem (State.addr base) w 1 ∧
      Outs (State.addr base) [(d, 4 * (4 * w + 2)), (o, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  rw [finishRecombine, WP.seq_iff]
  refine WP.mono (crt_finishPad_ready s h) ?_
  rintro u ⟨ready, product, low, outside, frame, restU⟩
  refine WP.mono (crt_addWide_ok u ready) ?_
  rintro t ⟨value, outsideT, frameT, ptrT, restT⟩
  rw [product, low] at value
  exact ⟨value, (Outs.of_outside outside (by simp)).trans (Outs.of_outside outsideT (by simp)),
    frame.trans frameT, ptrT, restU.trans restT⟩

end VG.Proof.Bignum.Arm

end

end

/-! # Multiplying h and q establishes the final CRT addition precondition -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtPadAfterProduct.lean`, which only this module imported.
section

/-! # Recombination multiplication preserves the source for padded residue export -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem CrtPadInput.after_product {s t : State} {base : BitVec 32} {size len w d product j : Nat}
    (h : CrtPadInput base size len w d s) (sep : 8 * len ≤ product) (hj : j < 8)
    (outside : Outs (State.addr base) [(128, 20), (product, 4 * (4 * w + 2))] s.mem t.mem)
    (frame : Frame [⟨State.addr base, size⟩] s.mem t.mem) (ptr : t.gpr .r0 = base)
    (rest : Rest roundClobbers s t) :
    CrtPadInput base size len w d t ∧ numAt t.mem (State.addr base) w j = numAt s.mem (State.addr base) w j := by
  have small := h.layout.size
  have nowrap := h.workspace.nowrap
  have head := control_buffers_header outside (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega)
  have link : t.mem.readW (off (State.addr base) 240) 32 = s.mem.readW (off (State.addr base) 240) 32 := by
    apply outs_readW outside
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
    · omega
  refine ⟨⟨h.workspace.congr rest.wr, h.main.congr rest.wr, h.layout.of_header_eq head,
    h.separate, h.fits, ptr, link.trans h.link,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead,
    by rw [rest.sp]; exact h.stackSep, saved_base_kept frame h.stackSep h.saved rest.sp⟩, ?_⟩
  have fit : arrAt w 8 ≤ 8 * len := h.layout.width ▸ h.layout.layout.2.2.1
  have bound := Nat.le_trans (array_end_le hj) fit
  rw [numAt_native, numAt_native]
  apply outside.val32
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right; simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega
    · left; simp only; omega
  · have := h.main.nowrap; omega

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure CrtRecombineInput (base : BitVec 32) (size len w o a b cp cq d : Nat) (s : State) : Prop where
  multiplication : CrtProductInput base size o a b cp cq w s true
  padding : CrtPadInput base size len w d s
  row : RowCtx s base size o d (4 * w)
  mainBeforeProduct : 8 * len ≤ o
  productBeforePad : o + 4 * (4 * w + 2) ≤ d
  sumFits : val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) +
    numAt s.mem (State.addr base) w 1 < 2 ^ (32 * (4 * w + 2))

theorem crt_recombineProduct_ready (s : State) {base : BitVec 32} {size len w o a b cp cq d : Nat}
    (h : CrtRecombineInput base size len w o a b cp cq d s) :
    WP isa (factorProduct true) s fun t => CrtFinishInput base size len w o d t ∧
      val32 t.mem (State.addr base) o (4 * w + 2) =
        val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) ∧
      numAt t.mem (State.addr base) w 1 = numAt s.mem (State.addr base) w 1 ∧
      Outs (State.addr base) [(128, 20), (o, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (crt_factorProduct_ok s h.multiplication) ?_
  rintro t ⟨value, outside, ptr, frame, rest⟩
  rw [show 2 * w + 2 * w + 2 = 4 * w + 2 by omega_using []] at value outside
  obtain ⟨pad, residue⟩ := h.padding.after_product h.mainBeforeProduct (by decide : 1 < 8) outside frame ptr rest
  have small := h.padding.layout.size
  have sep := h.mainBeforeProduct
  have output : t.mem.readW (off (State.addr base) 232) 32 = s.mem.readW (off (State.addr base) 232) 32 := by
    apply outs_readW outside
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith
    · omega_using []
  refine ⟨⟨pad, ⟨h.row.nowrap, h.row.outFits, h.row.inFits, h.row.separate,
    by rw [rest.wr]; exact h.row.writable⟩,
    by have := h.multiplication.outFits; omega_using [this], h.productBeforePad, output.trans h.multiplication.product, ?_⟩,
    value, residue, outside, frame, rest⟩
  rw [value, residue]
  exact h.sumFits

end VG.Proof.Bignum.Arm

end

end

/-! # The extended product buffers contain every possible CRT reconstruction -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

theorem crt_wideSum_fits {a b c w : Nat} (ha : a < 2 ^ (64 * w))
    (hb : b < 2 ^ (64 * w)) (hc : c < 2 ^ (64 * w)) :
    a * b + c < 2 ^ (32 * (4 * w + 2)) := by
  let R := 2 ^ (64 * w)
  have positive : 0 < R := Nat.two_pow_pos _
  have product : a * b ≤ R * R := Nat.mul_le_mul (Nat.le_of_lt ha) (Nat.le_of_lt hb)
  have square : R ≤ R * R := by
    have := Nat.mul_le_mul_left R (by omega_using [positive] : 1 ≤ R)
    simpa only [Nat.mul_one] using this
  have twice : R * R + R * R ≤ R * R * 2 ^ 64 := by
    have := Nat.mul_le_mul_left (R * R) (by decide : 2 ≤ 2 ^ 64)
    simpa only [Nat.mul_two] using this
  have bound : a * b + c < R * R * 2 ^ 64 := by omega_using [hc, product, square]
  simpa only [show 32 * (4 * w + 2) = (64 * w + 64 * w) + 64 by omega_using [], Nat.pow_add] using bound

theorem CrtShared.recombine_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    CrtRecombineInput g.base g.size (workspaceWords g.words) g.words (productOffset g.words)
      (crtProductA g.words true) (crtProductB g.words) (pOffset g.words) (qOffset g.words) (modulusOffset g.words) s := by
  have size := h.buffers.storageFits
  have fits : modulusOffset g.words + 4 * (4 * g.words + 2) ≤ g.size := Nat.le_trans (crt_modulus_end_le _) size
  have sep : productOffset g.words + 4 * (4 * g.words + 2) ≤ modulusOffset g.words := by
    simp only [modulusOffset, compareOffset, productBytes, productWords]; omega_using []
  refine ⟨h.product_input ready true, h.pad_input ready,
    ⟨h.buffers.workspace.nowrap, by omega_using [fits, sep], by omega_using [fits], Or.inl (by omega_using [sep]), h.buffers.workspace.writable⟩,
    by simp only [productOffset, stride]; omega_using [], sep, ?_⟩
  apply crt_wideSum_fits
  · simpa only [show 32 * (2 * g.words) = 64 * g.words by omega_using []] using
      val32_lt s.mem (State.addr g.base) (crtProductA g.words true) (2 * g.words)
  · simpa only [show 32 * (2 * g.words) = 64 * g.words by omega_using []] using
      val32_lt s.mem (State.addr g.base) (crtProductB g.words) (2 * g.words)
  · rw [numAt_native]
    simpa only [show 32 * (2 * g.words) = 64 * g.words by omega_using []] using
      val32_lt s.mem (State.addr g.base) (Proof.Rsa.Mont.arrAt g.words 1) (2 * g.words)

end VG.Proof.Bignum.Arm

end

end

/-! # Reconstruct the integer result from the coefficient and q residue -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtRecombine.lean`, which only this module imported.
section

/-! # Exact wide CRT reconstruction, including all buffer initialization -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_recombine_ok (s : State) {base : BitVec 32} {size len w o a b cp cq d : Nat}
    (h : CrtRecombineInput base size len w o a b cp cq d s) :
    WP isa recombine s fun t =>
      val32 t.mem (State.addr base) o (4 * w + 2) =
        val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) +
        numAt s.mem (State.addr base) w 1 ∧
      Outs (State.addr base) [(128, 20), (o, 4 * (4 * w + 2)), (d, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  rw [recombine, WP.seq_iff]
  refine WP.mono (crt_recombineProduct_ready s h) ?_
  rintro u ⟨ready, product, residue, outside, frame, rest⟩
  refine WP.mono (crt_finishRecombine_ok u ready) ?_
  rintro t ⟨value, outsideT, frameT, ptrT, restT⟩
  rw [product, residue] at value
  refine ⟨value, (outside.mono ?_).trans (outsideT.mono ?_), frame.trans frameT, ptrT, rest.trans restT⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_recombineStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa (.seq (.seq (.block CrtFn.qSource) (transferArray 1 6)) recombine) s fun t =>
      CrtShared g bs t ∧ LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      val32 t.mem (State.addr g.base) (productOffset g.words) (4 * g.words + 2) =
        numAt s.mem (State.addr (crtP g.base g.words)) g.words 5 *
        numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 +
        numAt s.mem (State.addr (crtQ g.base g.words)) g.words 6 ∧
      Frame [⟨State.addr g.base, g.size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (crt_importFinalResidue_ok s h ready) ?_
  rintro u ⟨sharedU, readyU, residue, frameU, restU⟩
  have pEq := h.workspace_eq_after h.buffers.context.p (by simp [crtRegions]) h.buffers.context.sepMP.symm (frameU.mono (by simp))
  have qEq := h.workspace_eq_after h.buffers.context.q (by simp [crtRegions]) h.buffers.context.sepMQ.symm (frameU.mono (by simp))
  refine WP.mono (crt_recombine_ok u (sharedU.recombine_input readyU)) ?_
  rintro t ⟨value, outside, frameT, ptr, restT⟩
  obtain ⟨pVal, qVal⟩ := sharedU.product_values true
  simp only [↓reduceIte] at pVal
  rw [pVal, qVal, pEq.number h.buffers.context.arraysFit (by decide : 5 < 8),
    qEq.number h.buffers.context.arraysFit (by decide : 0 < 8), residue] at value
  have writes : Outs (State.addr g.base) (crtValidationWrites g.words) u.mem t.mem := outside.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [crtValidationWrites])
  have sharedT := sharedU.after_validation writes frameT restT
  have readyT : LayoutFrameReady g.base (workspaceWords g.words) g.words t :=
    ⟨⟨sharedT.buffers.context.main, sharedT.main.layout, sharedT.main.width, ptr⟩,
      by rw [restT.rd, restT.wr, restT.sp]; exact readyU.stackRead,
      by rw [restT.sp]; exact readyU.stackSep,
      saved_base_kept frameT (sharedU.stack.separate.sub_left (Region.sub_prefix (by decide))) readyU.saved restT.sp⟩
  have frameU' : Frame [⟨State.addr g.base, g.size⟩] s.mem u.mem := frameU.sub (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact ⟨_, List.mem_singleton_self _, crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits (by simp [crtRegions])⟩)
  exact ⟨sharedT, readyT, value, frameU'.trans frameT, restU.trans restT⟩

end VG.Proof.Bignum.Arm
