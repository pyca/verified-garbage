module

public import VerifiedGarbage.Proof.Dsa.AArch64.CoreSign
public import VerifiedGarbage.Proof.Dsa.AArch64.PublicKey
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Dsa.AArch64.CheckOperands
import VerifiedGarbage.Proof.Dsa.AArch64.PublicCalls
import VerifiedGarbage.Proof.Dsa.Zero

/-! ### `Dsa.AArch64.PrivateKey`, which this module and modules that import it used -/

section

/-! # Private-key consistency and nonce-range validation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem privateKey_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hop : L.modulus % 2 = 1)
    {gb yb xb nb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator gb)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hx : OperandBytes s0 L.base usedBytes Core.privateScalar xb)
    (hn : OperandBytes s0 L.base usedBytes Core.nonce nb)
    (hgl : gb.length = L.pLen) (hyl : yb.length = L.pLen)
    (hxl : xb.length = L.qLen) (hnl : nb.length = L.qLen)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.privateKey M.mm) s0 fun s4 =>
      Ready L s4 ∧
      word s4.mem L.base Field.mask.offset =
        mask (decide (Spec.Dsa.encodeBE L.pLen (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE xb) L.modulus) = yb) &&
          (decide (0 < Spec.Dsa.decodeBE nb ∧ Spec.Dsa.decodeBE nb < L.subgroup) &&
          (decide (0 < Spec.Dsa.decodeBE xb ∧ Spec.Dsa.decodeBE xb < L.subgroup) && valid))) ∧
      Spec.Rsa.bytesAt s4.mem (off L.base qMinusTwo) L.qLen = Spec.Rsa.bytesAt s0.mem (off L.base qMinusTwo) L.qLen ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s4.mem ∧ Keep coreRegs s0 s4 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  obtain ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega_using [hpu]
  obtain hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega_using [hqu]
  obtain hqm0 := h0.readLocal .q qMinusTwo (by decide) hqm
  obtain hqml : (Spec.Rsa.bytesAt s0.mem (off L.base qMinusTwo) (ModulusSide.q.length L)).length = L.qLen := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, ModulusSide.length]
  unfold Checks.privateKey
  refine WP.seq (WP.mono (readyRange_ok h0 .q Core.privateScalar (by trivial) hx.active
    (by rw [hxl]; omega_using [hql]) (by simp only [hxl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm) fun s1 h1 => ?_)
  obtain hqm1 := h1.preserve h0 (Nat.le_refl _) (by decide) (by trivial) hqm0
  obtain hg1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg
  obtain hy1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy
  obtain hx1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.privateScalar]) hx
  obtain hn1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.nonce]) hn
  refine WP.seq (WP.mono (readyRange_ok h1.ready .q Core.nonce (by trivial) hn1.active
    (by rw [hnl]; omega_using [hql]) (by simp only [hnl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false h1.mask) fun s2 h2 => ?_)
  obtain hqm2 := h2.preserve h1.ready (Nat.le_refl _) (by decide) (by trivial) hqm1
  obtain hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  obtain hy2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy1
  obtain hx2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.privateScalar]) hx1
  refine WP.seq (WP.mono (readyPow_ok M h2.ready .p hp hop Core.generator Core.privateScalar (by trivial) (by trivial)
    hg2.active hx2.active (by rw [hgl]; omega_using [hql, hqp])
    (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hxl]; omega_using [hql]) (by rw [hxl]; omega_using [hqu]) t (by decide) ht) fun s3 h3 => ?_)
  obtain hqm3 := h3.local (by decide) ht hqm2 (by rw [hqml]; exact hqm)
    (Or.inl (by rw [hqml]; unfold qMinusTwo t; omega_using [hqu]))
  obtain hy3 := h3.external (by decide) ht hy2
  obtain hm3 := (h3.fields (by decide) ht .mask).trans h2.mask
  refine WP.mono (readyEqual_ok h3.ready (Core.element t) Core.publicValue
    (by change t < 2 ^ 16; decide) (by trivial) (h3.output (by decide) ht) hy3.active
    (by simp only [encodeBE_length, ModulusSide.length, hyl])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql, hqp])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hpu]) false hm3) fun s4 h4 => ?_
  obtain hqm4 := h4.preserve h3.ready (Nat.le_refl _) (by decide) (by trivial) hqm3
  obtain hqm4bytes := operand_bytesAt hqm4
  rw [hqml] at hqm4bytes
  refine ⟨h4.ready, ?_, hqm4bytes, ((h1.scheduleFrame.trans h2.scheduleFrame).trans (h3.scheduleFrame (by decide) ht)).trans h4.scheduleFrame,
    (((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep).mono (by decide)⟩
  have hm4 := h4.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length, ModulusSide.value] at hm4
  exact hm4

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.SigningKey`, which this module and modules that import it used -/

section

/-! # DSA signing domain validation without a redundant public-value power -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def signingKeyAccepted (L : ExecutionLayout) (gb yb : List Byte) (valid : Bool) : Bool :=
  decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) L.subgroup L.modulus = 1) &&
  (decide ((L.modulus - 1) % L.subgroup = 0) &&
  (decide (1 < Spec.Dsa.decodeBE yb ∧ Spec.Dsa.decodeBE yb < L.modulus) &&
  (decide (1 < Spec.Dsa.decodeBE gb ∧ Spec.Dsa.decodeBE gb < L.modulus) && valid)))

theorem signingKey_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
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
    WP isa (Checks.signingKey M.mm) s0 fun s8 =>
      Ready L s8 ∧ word s8.mem L.base Field.mask.offset = mask (signingKeyAccepted L gb yb valid) ∧
      OperandBytes s8 L.base activeBytes (Core.scalar qMinusTwo) (Spec.Dsa.encodeBE L.qLen (L.subgroup - 2)) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s8.mem ∧ Keep coreRegs s0 s8 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  have fitq (n : Nat) (h : n < L.subgroup) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.qLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hqf)
  have fitp (n : Nat) (h : n < L.modulus) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.pLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hpf)
  obtain ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega_using [hpu]
  obtain hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega_using [hqu]
  obtain hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega_using [hqu]
  unfold Checks.signingKey Checks.publicPrefix
  refine WP.seq (WP.mono (readyRange_ok h0 .p Core.generator (by trivial) hg.active
    (by rw [hgl]; omega_using [hql, hqp]) (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true hm) fun s1 h1 => ?_)
  obtain hg1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg
  obtain hy1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy
  obtain hq1 := h1.preserve h0 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb
  refine WP.seq (WP.mono (readyRange_ok h1.ready .p Core.publicValue (by trivial) hy1.active
    (by rw [hyl]; omega_using [hql, hqp]) (by simp only [hyl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true h1.mask) fun s2 h2 => ?_)
  obtain hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  obtain hq2 := h2.preserve h1.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq1
  refine WP.seq (WP.mono (readyMinus_ok h2.ready .p 1 (by decide) (by change 1 ≤ L.modulus; omega_using [hp])
    t (by decide) ht) fun s3 h3 => ?_)
  obtain hg3 := h3.external (by decide) ht hg2
  obtain hq3 := h3.external (by decide) ht hq2
  obtain hm3 := (h3.fields (by decide) ht .mask).trans h2.mask
  obtain step4 := readyReduce_ok M h3.ready hq hoq (Core.element t) (by change t < 2 ^ 16; decide)
    (h3.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hpu]) u (by decide) hu
  obtain step4' : WP isa (Core.reduce M.mm (Core.element t) (Core.scalar u)) s3
      (CallResult L .q u ((L.modulus - 1) % L.subgroup) s3) := by
    simpa only [ModulusSide.length, ModulusSide.value, fitp (L.modulus - 1) (by omega_using [hp])] using step4
  refine WP.seq (WP.mono step4' fun s4 h4 => ?_)
  obtain hg4 := h4.external (by decide) hu hg3
  obtain hq4 := h4.external (by decide) hu hq3
  obtain hm4 := (h4.fields (by decide) hu .mask).trans hm3
  refine WP.seq (WP.mono (readyZero_ok h4.ready (Core.scalar u) (by change u < 2 ^ 16; decide)
    (h4.output (by decide) hu) (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hqu]) false hm4) fun s5 h5 => ?_)
  obtain hziff : (∀ b ∈ Spec.Dsa.encodeBE L.qLen ((L.modulus - 1) % L.subgroup), b = 0) ↔
      (L.modulus - 1) % L.subgroup = 0 := by
    rw [← VG.Proof.Dsa.decodeBE_eq_zero, fitq _ (Nat.mod_lt _ (by omega_using [hq]))]
  have hm5 := h5.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length] at hm5
  simp only [hziff] at hm5
  obtain hg5 := h5.preserve h4.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg4
  obtain hq5 := h5.preserve h4.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq4
  refine WP.seq (WP.mono (readyMinus_ok h5.ready .q 2 (by decide) (by change 2 ≤ L.subgroup; omega_using [hq])
    qMinusTwo (by decide) hqm) fun s6 h6 => ?_)
  obtain hg6 := h6.external (by decide) hqm hg5
  obtain hq6 := h6.external (by decide) hqm hq5
  obtain hm6 := (h6.fields (by decide) hqm .mask).trans hm5
  obtain step7 := readyPublicPow_ok M h6.ready .p hp hop Core.generator ⟨.input .q, .qLen⟩ (by trivial) (by trivial)
    hg6.active hq6.active (by rw [hgl]; omega_using [hql, hqp])
    (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hqlen]; omega_using [hql]) (by rw [hqlen]; omega_using [hqu]) t (by decide) ht
  obtain step7' : WP isa (Core.publicPow M.mm pWorkspace Core.generator ⟨.input .q, .qLen⟩ (Core.element t)) s6
      (CallResult L .p t (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) L.subgroup L.modulus) s6) := by
    simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value, hqval] using step7
  refine WP.seq (WP.mono step7' fun s7 h7 => ?_)
  obtain hqm7 := h7.local (by decide) ht (h6.output (by decide) hqm)
    (by simp only [encodeBE_length, ModulusSide.length]; exact hqm)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold qMinusTwo t; omega_using [hqu]))
  obtain hm7 := (h7.fields (by decide) ht .mask).trans hm6
  refine WP.mono (readyIsOne_ok h7.ready .p (Core.element t) (by change t < 2 ^ 16; decide)
    (h7.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql, hqp])
    (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _) hm7) fun s8 h8 => ?_
  have hm8 := h8.mask
  simp only [ModulusSide.length, fitp _ (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hp]))] at hm8
  obtain hqm8 := h8.preserve h7.ready (Nat.le_refl _) (by decide) (by trivial) hqm7
  refine ⟨h8.ready, hm8, hqm8, ?_, ?_⟩
  · exact ((((((h1.scheduleFrame.trans h2.scheduleFrame).trans (h3.scheduleFrame (by decide) ht)).trans (h4.scheduleFrame (by decide) hu)).trans h5.scheduleFrame).trans
      (h6.scheduleFrame (by decide) hqm)).trans (h7.scheduleFrame (by decide) ht)).trans h8.scheduleFrame
  · have hk5 : Keep coreRegs s0 s5 :=
      ((((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep).trans h5.keep).mono (by decide)
    obtain hk8 : Keep coreRegs s5 s8 :=
      ((h6.keep.trans h7.keep).trans h8.keep).mono (by decide)
    exact (hk5.trans hk8).mono (by decide)

end VG.Proof.Dsa.AArch64

end

end

/-! # Signing computation, including every key and scalar rejection mask -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def privateAccepted (L : ExecutionLayout) (data : SignValues) (yb : List Byte) (valid : Bool) : Bool :=
  decide (Spec.Dsa.encodeBE L.pLen
    (Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) (Spec.Dsa.decodeBE data.privateScalar) L.modulus) = yb) &&
  (decide (0 < Spec.Dsa.decodeBE data.nonce ∧ Spec.Dsa.decodeBE data.nonce < L.subgroup) &&
  (decide (0 < Spec.Dsa.decodeBE data.privateScalar ∧ Spec.Dsa.decodeBE data.privateScalar < L.subgroup) &&
    publicAccepted L data.generator yb valid))

/-- The omitted public-value check follows from the generator check and the
private/public key equality, even when the domain integers are composite. -/
theorem privateAccepted_signingKey (L : ExecutionLayout) (data : SignValues)
    (yb : List Byte) (valid : Bool) (hp : 1 < L.modulus)
    (hpf : L.modulus ≤ 256 ^ L.pLen) :
    (decide (Spec.Dsa.encodeBE L.pLen
      (Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) (Spec.Dsa.decodeBE data.privateScalar) L.modulus) = yb) &&
    (decide (0 < Spec.Dsa.decodeBE data.nonce ∧ Spec.Dsa.decodeBE data.nonce < L.subgroup) &&
    (decide (0 < Spec.Dsa.decodeBE data.privateScalar ∧ Spec.Dsa.decodeBE data.privateScalar < L.subgroup) &&
      signingKeyAccepted L data.generator yb valid))) = privateAccepted L data yb valid := by
  by_cases he : Spec.Dsa.encodeBE L.pLen
      (Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) (Spec.Dsa.decodeBE data.privateScalar) L.modulus) = yb
  · by_cases hg : Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) L.subgroup L.modulus = 1
    · have hy : Spec.Dsa.decodeBE yb =
          Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) (Spec.Dsa.decodeBE data.privateScalar) L.modulus := by
        rw [← he, decodeBE_encodeBE (Nat.lt_of_lt_of_le (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hp])) hpf)]
      have hsub : Spec.Dsa.powMod (Spec.Dsa.decodeBE yb) L.subgroup L.modulus = 1 := by
        rw [hy, VG.Proof.Dsa.powMod_eq, VG.Proof.Dsa.powMod_eq, ← Nat.pow_mod,
          ← Nat.pow_mul, Nat.mul_comm (Spec.Dsa.decodeBE data.privateScalar) L.subgroup,
          Nat.pow_mul, Nat.pow_mod,
          ← VG.Proof.Dsa.powMod_eq (Spec.Dsa.decodeBE data.generator) L.subgroup L.modulus, hg]
        simp [Nat.mod_eq_of_lt hp]
      simp only [privateAccepted, publicAccepted, signingKeyAccepted, hsub, decide_true, Bool.true_and]
    · simp [privateAccepted, publicAccepted, signingKeyAccepted, hg]
  · simp [privateAccepted, he]

def signAccepted (L : ExecutionLayout) (data : SignValues) (yb : List Byte) (valid : Bool) : Bool :=
  !decide (∀ b ∈ Spec.Dsa.encodeBE L.qLen (data.s L), b = 0) &&
  (!decide (∀ b ∈ Spec.Dsa.encodeBE L.qLen (data.r L), b = 0) && privateAccepted L data yb valid)

def signCompute (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  Checks.signingKey mul, Checks.privateKey mul, Core.sign mul,
  Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true]

theorem signCompute_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : SignValues) {yb qb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator data.generator)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hqb : OperandBytes s0 L.base usedBytes ⟨.input .q, .qLen⟩ qb)
    (hx : OperandBytes s0 L.base usedBytes Core.privateScalar data.privateScalar)
    (hn : OperandBytes s0 L.base usedBytes Core.nonce data.nonce)
    (hz : OperandBytes s0 L.base usedBytes Core.digest data.digest)
    (hgl : data.generator.length = L.pLen) (hyl : yb.length = L.pLen) (hqlen : qb.length = L.qLen)
    (hxl : data.privateScalar.length = L.qLen) (hnl : data.nonce.length = L.qLen)
    (hzl : data.digest.length < 2 ^ 64) (hqval : Spec.Dsa.decodeBE qb = L.subgroup)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (signCompute M.mm) s0 fun s5 =>
      Ready L s5 ∧ word s5.mem L.base Field.mask.offset = mask (signAccepted L data yb valid) ∧
      Spec.Rsa.bytesAt s5.mem (off L.base r) L.qLen = Spec.Dsa.encodeBE L.qLen (data.r L) ∧
      Spec.Rsa.bytesAt s5.mem (off L.base s) L.qLen = Spec.Dsa.encodeBE L.qLen (data.s L) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s5.mem ∧ Keep coreRegs s0 s5 := by
  obtain ⟨hql, hqu, _, _⟩ := L.widths
  have hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega_using [hqu]
  have hr : r + L.qLen ≤ usedBytes := by unfold r usedBytes; omega_using [hqu]
  have hs : s + L.qLen ≤ usedBytes := by unfold s usedBytes; omega_using [hqu]
  unfold signCompute
  refine WP.seq (WP.mono (signingKey_ok M h0 hp hq hop hoq hpf hqf hg hy hqb hgl hyl hqlen hqval hm)
    fun s1 ⟨h1, hm1, hqm1, hf1, hk1⟩ => ?_)
  have hg1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.generator]) hg
  have hy1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.publicValue]) hy
  have hx1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.privateScalar]) hx
  have hn1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.nonce]) hn
  have hz1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.digest]) hz
  refine WP.seq (WP.mono (privateKey_ok M h1 hp hop hg1 hy1 hx1 hn1 hgl hyl hxl hnl hm1)
    fun s2 ⟨h2, hm2, hqm2bytes, hf2, hk2⟩ => ?_)
  rw [privateAccepted_signingKey L data yb valid hp hpf] at hm2
  have hg2 := h1.preserveExternal h2 hf2 hk2 (by decide) (by simp [stablePointer, Core.generator]) hg1
  have hx2 := h1.preserveExternal h2 hf2 hk2 (by decide) (by simp [stablePointer, Core.privateScalar]) hx1
  have hn2 := h1.preserveExternal h2 hf2 hk2 (by decide) (by simp [stablePointer, Core.nonce]) hn1
  have hz2 := h1.preserveExternal h2 hf2 hk2 (by decide) (by simp [stablePointer, Core.digest]) hz1
  have hqm1bytes := operand_bytesAt hqm1
  rw [encodeBE_length] at hqm1bytes
  have hqm2 := h2.encodedLocal .q qMinusTwo (L.subgroup - 2) (by decide) hqm (hqm2bytes.trans hqm1bytes)
  refine WP.seq (WP.mono (coreSign_ok M h2 hp hq hop hoq hpf hqf data hg2 hn2 hx2 hz2 hgl hnl hxl hzl hqm2)
    fun s3 ⟨h3, hr3bytes, hs3bytes, hf3, hm3eq, hk3⟩ => ?_)
  have hm3 : word s3.mem L.base Field.mask.offset = mask (privateAccepted L data yb valid) := hm3eq.trans hm2
  have hr3 := h3.encodedLocal .q r (data.r L) (by decide) hr hr3bytes
  have hs3 := h3.encodedLocal .q s (data.s L) (by decide) hs hs3bytes
  refine WP.seq (WP.mono (readyZero_ok h3 (Core.scalar r) (by change r < 2 ^ 16; decide) hr3
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hqu]) true hm3) fun s4 h4 => ?_)
  have hr4 := h4.preserve h3 (Nat.le_refl _) (by decide) (by trivial) hr3
  have hs4 := h4.preserve h3 (Nat.le_refl _) (by decide) (by trivial) hs3
  refine WP.mono (readyZero_ok h4.ready (Core.scalar s) (by change s < 2 ^ 16; decide) hs4
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hqu]) true h4.mask) fun s5 h5 => ?_
  have hr5 := h5.preserve h4.ready (Nat.le_refl _) (by decide) (by trivial) hr4
  have hs5 := h5.preserve h4.ready (Nat.le_refl _) (by decide) (by trivial) hs4
  refine ⟨h5.ready, ?_, ?_, ?_, (((hf1.trans hf2).trans hf3).trans h4.scheduleFrame).trans h5.scheduleFrame,
    ((((hk1.trans hk2).trans hk3).trans h4.keep).trans h5.keep).mono (by decide)⟩
  · have hm5 := h5.mask
    simp only [↓reduceIte, ModulusSide.length] at hm5
    exact hm5
  · have hh := operand_bytesAt hr5
    rw [encodeBE_length] at hh
    exact hh
  · have hh := operand_bytesAt hs5
    rw [encodeBE_length] at hh
    exact hh

end VG.Proof.Dsa.AArch64
