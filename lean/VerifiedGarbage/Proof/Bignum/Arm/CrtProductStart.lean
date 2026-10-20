module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductState
import VerifiedGarbage.Proof.Bignum.Arm.CrtProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn

/-! # Product arguments establish the full schoolbook-loop invariant -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtProductStart (base : BitVec 32) (size o a b w : Nat) (s : State) : Prop where
  context : WideProductCtx s base size o a b (2 * w) (2 * w)
  initial : WideProductInv s base o a b (2 * w) (2 * w) 0 s

theorem crt_productArgs_ready (s : State) {base : BitVec 32} {size o a b cp cq w : Nat} {coefficient : Bool}
    (h : CrtProductInput base size o a b cp cq w s coefficient)
    (zero : val32 s.mem (State.addr base) o (2 * w + 2 * w + 2) = 0) :
    WP isa (productArgs coefficient) s fun t => CrtProductStart base size o a b w t ∧
      Outside (State.addr base) 128 20 s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest [.r1] s t := by
  have outFit := h.outFits
  have beforeP := h.pBeforeOut
  have beforeQ := h.qBeforeOut
  refine WP.mono (crt_productArgs_ok s h.workspace h.parentFit h.qHeader (by omega) (by omega)
    h.ptr h.pLink h.qLink h.pArray h.qArray h.product h.count) ?_
  rintro t ⟨memT, rest⟩
  have result := crtProductMem_ok s.mem (State.addr base)
    (base + BitVec.ofNat 32 a) (base + BitVec.ofNat 32 b) (base + BitVec.ofNat 32 o)
    (BitVec.ofNat 32 (2 * w)) (BitVec.ofNat 32 (2 * w))
  dsimp only at result
  rw [← memT] at result
  obtain ⟨p, q, out, count, width, outside⟩ := result
  have frame := outside_workspace outside (size := size) h.headerFit
  have ctx := h.toWideProductCtx.after_frame rest frame
  have zeroT : val32 t.mem (State.addr base) o (2 * w + 2 * w + 2) = 0 := by
    rw [outside.val32 (by have := h.oHeader; omega) (by have := h.workspace.nowrap; omega), zero]
  refine ⟨⟨ctx, ?_⟩, outside, frame, rest⟩
  refine ⟨by omega, (rest.gpr .r0 (by simp)).trans h.ptr, ?_, q, ?_, ?_, width,
    Outs.refl _ _ _, ?_, Rest.refl _ _⟩
  · simpa only [Nat.mul_zero, Nat.add_zero] using p
  · simpa only [Nat.mul_zero, Nat.add_zero] using out
  · simpa only [Nat.sub_zero] using count
  · simp only [val32, Nat.zero_mul]; exact zeroT

end VG.Proof.Bignum.Arm
