module

import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulus
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCompareProduct
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusState
public import VerifiedGarbage.Impl.Bignum.Arm.CrtPadModulus
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase

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
    outside.val32 h.separate (by omega), value, outside, rest⟩
  · exact (outside_read32 outside (by omega) (by decide)).trans c.count
  · exact (outside_read32 outside (by omega) (by decide)).trans c.output
  · exact (outside_read32 outside (by omega) (by decide)).trans c.first
  · exact (outside_read32 outside (by omega) (by decide)).trans c.second
  · rw [rest.rd, rest.wr, rest.sp]; exact c.stackRead
  · rw [rest.sp]; exact c.stackSep
  · exact saved_base_kept frame c.stackSep c.saved rest.sp

end VG.Proof.Bignum.Arm
