module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtValidateProduct
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckProductState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductState

import VerifiedGarbage.Proof.Bignum.Arm.CrtFactorProduct
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.CrtCheckProduct
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.ControlBuffers
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
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

theorem crt_validationProduct_ready (s : State) {base : BitVec 32} {size len product cmp pad a b cp cq w : Nat}
    (h : CrtValidateInput base size len product cmp pad a b cp cq w s) :
    WP isa factorProduct s fun t => CrtCheckProductInput base size len cmp product pad w t ∧
      val32 t.mem (State.addr base) product (4 * w + 2) =
        val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) ∧
      Proof.Rsa.Mont.numAt t.mem (State.addr base) w 0 = Proof.Rsa.Mont.numAt s.mem (State.addr base) w 0 ∧
      Outs (State.addr base) [(128, 20), (product, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (crt_factorProduct_ok s h.multiplication) ?_
  rintro t ⟨value, outside, ptr, frame, rest⟩
  rw [show 2 * w + 2 * w + 2 = 4 * w + 2 by omega] at value outside
  obtain ⟨ready, modulus⟩ := h.comparison.after_product h.separate outside frame ptr rest
  exact ⟨ready, value, modulus, outside, frame, rest⟩

theorem crt_validateProduct_ok (s : State) {base : BitVec 32} {size len product cmp pad a b cp cq w : Nat}
    (h : CrtValidateInput base size len product cmp pad a b cp cq w s) :
    WP isa validateProduct s fun t =>
      t.gpr .r11 = (if val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) =
        Proof.Rsa.Mont.numAt s.mem (State.addr base) w 0 then 1 else 0) ∧
      Outs (State.addr base) [(128, 20), (product, 4 * (4 * w + 2)),
        (pad, 4 * (4 * w + 2)), (cmp, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  rw [validateProduct, WP.seq_iff]
  refine WP.mono (crt_validationProduct_ready s h) ?_
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

end VG.Proof.Bignum.Arm
