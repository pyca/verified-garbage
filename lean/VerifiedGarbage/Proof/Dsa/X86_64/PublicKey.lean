module

public import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
import VerifiedGarbage.Proof.Dsa.X86_64.PublicCalls
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Algebraic domain and public-key validation for DSA -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def publicAccepted (L : ExecutionLayout) (gb yb : List Byte) (valid : Bool) : Bool :=
  decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE yb) L.subgroup L.modulus = 1) &&
  (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) L.subgroup L.modulus = 1) &&
  (decide ((L.modulus - 1) % L.subgroup = 0) &&
  (decide (1 < Spec.Dsa.decodeBE yb ∧ Spec.Dsa.decodeBE yb < L.modulus) &&
  (decide (1 < Spec.Dsa.decodeBE gb ∧ Spec.Dsa.decodeBE gb < L.modulus) && valid))))

theorem publicKey_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb yb qb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator gb)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hqb : OperandBytes s0 L.base usedBytes ⟨.input .q, .qLen⟩ qb)
    (hgl : gb.length = L.pLen) (hyl : yb.length = L.pLen) (hqlen : qb.length = L.qLen)
    (hqval : Spec.Dsa.decodeBE qb = L.subgroup)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.publicKey Sq.mm M.mm) s0 fun s10 =>
      Ready L s10 ∧ word s10.mem L.base Field.mask.offset = mask (publicAccepted L gb yb valid) ∧
      OperandBytes s10 L.base activeBytes (Core.scalar qMinusTwo) (Spec.Dsa.encodeBE L.qLen (L.subgroup - 2)) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s10.mem ∧ Keep coreRegs s0 s10 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  have fitq (n : Nat) (h : n < L.subgroup) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.qLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hqf)
  have fitp (n : Nat) (h : n < L.modulus) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.pLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hpf)
  have ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega
  have hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega
  have hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega
  unfold Checks.publicKey Checks.publicPrefix
  refine WP.seq (WP.mono (readyRange_ok h0 .p Core.generator (by trivial) hg.active
    (by rw [hgl]; omega) (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true hm) fun s1 h1 => ?_)
  have hg1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg
  have hy1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy
  have hq1 := h1.preserve h0 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb
  refine WP.seq (WP.mono (readyRange_ok h1.ready .p Core.publicValue (by trivial) hy1.active
    (by rw [hyl]; omega) (by simp only [hyl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true h1.mask) fun s2 h2 => ?_)
  have hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  have hy2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy1
  have hq2 := h2.preserve h1.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq1
  refine WP.seq (WP.mono (readyMinus_ok h2.ready .p 1 (by decide) (by change 1 ≤ L.modulus; omega)
    t (by decide) ht) fun s3 h3 => ?_)
  have hg3 := h3.external (by decide) ht hg2
  have hy3 := h3.external (by decide) ht hy2
  have hq3 := h3.external (by decide) ht hq2
  have hm3 := (h3.fields (by decide) ht .mask).trans h2.mask
  have step4 := readyReduce_ok M h3.ready hq hoq (Core.element t) (by change t < 2 ^ 31; decide)
    (h3.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega) u (by decide) hu
  have step4' : WP isa (Core.reduce M.mm (Core.element t) (Core.scalar u)) s3
      (CallResult L .q u ((L.modulus - 1) % L.subgroup) s3) := by
    simpa only [ModulusSide.length, ModulusSide.value, fitp (L.modulus - 1) (by omega)] using step4
  refine WP.seq (WP.mono step4' fun s4 h4 => ?_)
  have hg4 := h4.external (by decide) hu hg3
  have hy4 := h4.external (by decide) hu hy3
  have hq4 := h4.external (by decide) hu hq3
  have hm4 := (h4.fields (by decide) hu .mask).trans hm3
  refine WP.seq (WP.mono (readyZero_ok h4.ready (Core.scalar u) (by change u < 2 ^ 31; decide)
    (h4.output (by decide) hu) (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) false hm4) fun s5 h5 => ?_)
  have hziff : (∀ b ∈ Spec.Dsa.encodeBE L.qLen ((L.modulus - 1) % L.subgroup), b = 0) ↔
      (L.modulus - 1) % L.subgroup = 0 := by
    rw [← VG.Proof.Dsa.decodeBE_eq_zero, fitq _ (Nat.mod_lt _ (by omega))]
  have hm5 := h5.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length] at hm5
  simp only [hziff] at hm5
  have hg5 := h5.preserve h4.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg4
  have hy5 := h5.preserve h4.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy4
  have hq5 := h5.preserve h4.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq4
  refine WP.seq (WP.mono (readyMinus_ok h5.ready .q 2 (by decide) (by change 2 ≤ L.subgroup; omega)
    qMinusTwo (by decide) hqm) fun s6 h6 => ?_)
  have hg6 := h6.external (by decide) hqm hg5
  have hy6 := h6.external (by decide) hqm hy5
  have hq6 := h6.external (by decide) hqm hq5
  have hm6 := (h6.fields (by decide) hqm .mask).trans hm5
  have step7 := readyPublicPow_ok M Sq h6.ready .p hp hop Core.generator ⟨.input .q, .qLen⟩ (by trivial) (by trivial)
    hg6.active hq6.active (by rw [hgl]; omega)
    (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hqlen]; omega) (by rw [hqlen]; omega) t (by decide) ht
  have step7' : WP isa (Core.publicPow Sq.mm M.mm pWorkspace Core.generator ⟨.input .q, .qLen⟩ (Core.element t)) s6
      (CallResult L .p t (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) L.subgroup L.modulus) s6) := by
    simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value, hqval] using step7
  refine WP.seq (WP.mono step7' fun s7 h7 => ?_)
  have hy7 := h7.external (by decide) ht hy6
  have hq7 := h7.external (by decide) ht hq6
  have hqm7 := h7.local (by decide) ht (h6.output (by decide) hqm)
    (by simp only [encodeBE_length, ModulusSide.length]; exact hqm)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold qMinusTwo t; omega))
  have hm7 := (h7.fields (by decide) ht .mask).trans hm6
  refine WP.seq (WP.mono (readyIsOne_ok h7.ready .p (Core.element t) (by change t < 2 ^ 31; decide)
    (h7.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _) hm7) fun s8 h8 => ?_)
  have hm8 := h8.mask
  simp only [ModulusSide.length, fitp _ (VG.Proof.Dsa.powMod_lt _ _ (by omega))] at hm8
  have hy8 := h8.preserve h7.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy7
  have hq8 := h8.preserve h7.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq7
  have hqm8 := h8.preserve h7.ready (Nat.le_refl _) (by decide) (by trivial) hqm7
  have step9 := readyPublicPow_ok M Sq h8.ready .p hp hop Core.publicValue ⟨.input .q, .qLen⟩ (by trivial) (by trivial)
    hy8.active hq8.active (by rw [hyl]; omega)
    (by simp only [hyl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hqlen]; omega) (by rw [hqlen]; omega) t (by decide) ht
  have step9' : WP isa (Core.publicPow Sq.mm M.mm pWorkspace Core.publicValue ⟨.input .q, .qLen⟩ (Core.element t)) s8
      (CallResult L .p t (Spec.Dsa.powMod (Spec.Dsa.decodeBE yb) L.subgroup L.modulus) s8) := by
    simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value, hqval] using step9
  refine WP.seq (WP.mono step9' fun s9 h9 => ?_)
  have hqm9 := h9.local (by decide) ht hqm8
    (by simp only [encodeBE_length, ModulusSide.length]; exact hqm)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold qMinusTwo t; omega))
  have hm9 := (h9.fields (by decide) ht .mask).trans hm8
  refine WP.mono (readyIsOne_ok h9.ready .p (Core.element t) (by change t < 2 ^ 31; decide)
    (h9.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _) hm9) fun s10 h10 => ?_
  have hqm10 := h10.preserve h9.ready (Nat.le_refl _) (by decide) (by trivial) hqm9
  refine ⟨h10.ready, ?_, hqm10, ?_, ?_⟩
  · have hm10 := h10.mask
    simp only [ModulusSide.length, ModulusSide.value,
      fitp _ (VG.Proof.Dsa.powMod_lt _ _ (by omega))] at hm10
    exact hm10
  · exact ((((((((h1.scheduleFrame.trans h2.scheduleFrame).trans (h3.scheduleFrame (by decide) ht)).trans (h4.scheduleFrame (by decide) hu)).trans h5.scheduleFrame).trans
      (h6.scheduleFrame (by decide) hqm)).trans (h7.scheduleFrame (by decide) ht)).trans h8.scheduleFrame).trans (h9.scheduleFrame (by decide) ht)).trans h10.scheduleFrame
  · have hk5 : Keep coreRegs s0 s5 :=
      ((((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep).trans h5.keep).mono (by decide)
    have hk10 : Keep coreRegs s5 s10 :=
      ((((h6.keep.trans h7.keep).trans h8.keep).trans h9.keep).trans h10.keep).mono (by decide)
    exact (hk5.trans hk10).mono (by decide)

end VG.Proof.Dsa.X86_64
