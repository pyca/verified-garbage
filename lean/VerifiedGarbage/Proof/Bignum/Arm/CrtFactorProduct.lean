module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductState

import VerifiedGarbage.Proof.Bignum.Arm.CrtProductStart
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.WideProduct
import VerifiedGarbage.Proof.Bignum.Arm.WideProductState
import VerifiedGarbage.Proof.Bignum.Arm.WideProductBody
import VerifiedGarbage.Impl.Bignum.Arm.Zero
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

theorem crt_factorProduct_ok (s : State) {base : BitVec 32} {size o a b cp cq w : Nat} {coefficient : Bool}
    (h : CrtProductInput base size o a b cp cq w s coefficient) :
    WP isa (factorProduct coefficient) s fun t =>
      val32 t.mem (State.addr base) o (2 * w + 2 * w + 2) =
        val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) ∧
      Outs (State.addr base) [(128, 20), (o, 4 * (2 * w + 2 * w + 2))] s.mem t.mem ∧
      t.gpr .r0 = base ∧ Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have nowrap := h.workspace.nowrap
  have aFits := h.aFits
  have bFits := h.bFits
  have aHeader := h.aHeader
  have bHeader := h.bHeader
  rw [factorProduct, WP.seq_iff]
  refine WP.mono (crt_productClear_ready s h) ?_
  rintro u ⟨inputU, zeroU, outsideU, frameU, restU⟩
  have aU := outsideU.val32 (d := a) (k := 2 * w) h.separateA.symm (by omega)
  have bU := outsideU.val32 (d := b) (k := 2 * w) h.separateB.symm (by omega)
  rw [WP.seq_iff]
  refine WP.mono (crt_productArgs_ready u inputU zeroU) ?_
  rintro v ⟨start, outsideV, frameV, restV⟩
  have aV := outsideV.val32 (d := a) (k := 2 * w) (by omega) (by omega)
  have bV := outsideV.val32 (d := b) (k := 2 * w) (by omega) (by omega)
  have initial := start.initial
  have p := initial.aPtr
  have out := initial.oPtr
  have count := initial.count
  have zero := initial.value
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, val32, Nat.zero_mul] at p out count zero
  refine WP.mono (wideProduct_ok v start.context initial.ptr p initial.bPtr out count initial.width zero) ?_
  rintro t ⟨value, outsideT, ptrT, frameT, restT⟩
  rw [aV, bV, aU, bU] at value
  have widened : Outs (State.addr base) [(128, 20), (o, 4 * (2 * w + 2 * w + 2))] v.mem t.mem := by
    intro x hx
    apply outsideT x
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hfirst := hx (128, 20) (by simp)
      omega
    · exact hx _ (by simp)
  exact ⟨value, (Outs.of_outside outsideU (by simp)).trans ((Outs.of_outside outsideV (by simp)).trans widened),
    ptrT, frameU.trans (frameV.trans frameT), restU.trans ((restV.mono (by decide)).trans restT)⟩

end VG.Proof.Bignum.Arm
