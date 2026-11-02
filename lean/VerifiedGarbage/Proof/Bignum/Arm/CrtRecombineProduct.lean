module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtFinishRecombine
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductState

import VerifiedGarbage.Proof.Bignum.Arm.CrtFactorProduct
import VerifiedGarbage.Proof.Bignum.Arm.ControlBuffers
import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusState
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
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
  rw [show 2 * w + 2 * w + 2 = 4 * w + 2 by omega] at value outside
  obtain ⟨pad, residue⟩ := h.padding.after_product h.mainBeforeProduct (by decide : 1 < 8) outside frame ptr rest
  have small := h.padding.layout.size
  have sep := h.mainBeforeProduct
  have output : t.mem.readW (off (State.addr base) 232) 32 = s.mem.readW (off (State.addr base) 232) 32 := by
    apply outs_readW outside
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
    · omega
  refine ⟨⟨pad, ⟨h.row.nowrap, h.row.outFits, h.row.inFits, h.row.separate,
    by rw [rest.wr]; exact h.row.writable⟩,
    by have := h.multiplication.outFits; omega, h.productBeforePad, output.trans h.multiplication.product, ?_⟩,
    value, residue, outside, frame, rest⟩
  rw [value, residue]
  exact h.sumFits

end VG.Proof.Bignum.Arm
