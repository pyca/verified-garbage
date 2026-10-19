module
public import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands

import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Private-key consistency and nonce-range validation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem privateKey_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hop : L.modulus % 2 = 1)
    {gb yb xb nb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator gb)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hx : OperandBytes s0 L.base usedBytes Core.privateScalar xb)
    (hn : OperandBytes s0 L.base usedBytes Core.nonce nb)
    (hgl : gb.length = L.pLen) (hyl : yb.length = L.pLen)
    (hxl : xb.length = L.qLen) (hnl : nb.length = L.qLen)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.privateKey Sq.mm M.mm) s0 fun s4 =>
      Ready L s4 ∧
      word s4.mem L.base Field.mask.offset =
        mask (decide (Spec.Dsa.encodeBE L.pLen (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE xb) L.modulus) = yb) &&
          (decide (0 < Spec.Dsa.decodeBE nb ∧ Spec.Dsa.decodeBE nb < L.subgroup) &&
          (decide (0 < Spec.Dsa.decodeBE xb ∧ Spec.Dsa.decodeBE xb < L.subgroup) && valid))) ∧
      Spec.Rsa.bytesAt s4.mem (off L.base qMinusTwo) L.qLen = Spec.Rsa.bytesAt s0.mem (off L.base qMinusTwo) L.qLen ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s4.mem ∧ Keep coreRegs s0 s4 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  have ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega
  have hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega
  have hqm0 := h0.readLocal .q qMinusTwo (by decide) hqm
  have hqml : (Spec.Rsa.bytesAt s0.mem (off L.base qMinusTwo) (ModulusSide.q.length L)).length = L.qLen := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, ModulusSide.length]
  unfold Checks.privateKey
  refine WP.seq (WP.mono (readyRange_ok h0 .q Core.privateScalar (by trivial) hx.active
    (by rw [hxl]; omega) (by simp only [hxl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm) fun s1 h1 => ?_)
  have hqm1 := h1.preserve h0 (Nat.le_refl _) (by decide) (by trivial) hqm0
  have hg1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg
  have hy1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy
  have hx1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.privateScalar]) hx
  have hn1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.nonce]) hn
  refine WP.seq (WP.mono (readyRange_ok h1.ready .q Core.nonce (by trivial) hn1.active
    (by rw [hnl]; omega) (by simp only [hnl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false h1.mask) fun s2 h2 => ?_)
  have hqm2 := h2.preserve h1.ready (Nat.le_refl _) (by decide) (by trivial) hqm1
  have hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  have hy2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy1
  have hx2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.privateScalar]) hx1
  refine WP.seq (WP.mono (readyPow_ok M Sq h2.ready .p hp hop Core.generator Core.privateScalar (by trivial) (by trivial)
    hg2.active hx2.active (by rw [hgl]; omega)
    (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hxl]; omega) (by rw [hxl]; omega) t (by decide) ht) fun s3 h3 => ?_)
  have hqm3 := h3.local (by decide) ht hqm2 (by rw [hqml]; exact hqm)
    (Or.inl (by rw [hqml]; unfold qMinusTwo t; omega))
  have hy3 := h3.external (by decide) ht hy2
  have hm3 := (h3.fields (by decide) ht .mask).trans h2.mask
  refine WP.mono (readyEqual_ok h3.ready (Core.element t) Core.publicValue
    (by change t < 2 ^ 31; decide) (by trivial) (h3.output (by decide) ht) hy3.active
    (by simp only [encodeBE_length, ModulusSide.length, hyl])
    (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) false hm3) fun s4 h4 => ?_
  have hqm4 := h4.preserve h3.ready (Nat.le_refl _) (by decide) (by trivial) hqm3
  have hqm4bytes := operand_bytesAt hqm4
  rw [hqml] at hqm4bytes
  refine ⟨h4.ready, ?_, hqm4bytes, ((h1.scheduleFrame.trans h2.scheduleFrame).trans (h3.scheduleFrame (by decide) ht)).trans h4.scheduleFrame,
    (((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep).mono (by decide)⟩
  have hm4 := h4.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length, ModulusSide.value] at hm4
  exact hm4

end VG.Proof.Dsa.X86_64
