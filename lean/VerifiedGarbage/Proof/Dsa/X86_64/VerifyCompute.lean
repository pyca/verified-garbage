module

public import VerifiedGarbage.Proof.Dsa.X86_64.CoreVerify
public import VerifiedGarbage.Proof.Dsa.X86_64.PublicKey
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Verification computation, including domain, key and signature checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def verifyAccepted (L : ExecutionLayout) (data : VerifyValues) (valid : Bool) : Bool :=
  decide (Spec.Dsa.encodeBE L.qLen (data.value L) = data.signatureR) &&
  (decide (0 < Spec.Dsa.decodeBE data.signatureS ∧ Spec.Dsa.decodeBE data.signatureS < L.subgroup) &&
  (decide (0 < Spec.Dsa.decodeBE data.signatureR ∧ Spec.Dsa.decodeBE data.signatureR < L.subgroup) &&
    publicAccepted L data.generator data.publicValue valid))

def verifyCompute (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  Checks.publicKey sq mul, Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
  Core.verify sq mul, Checks.equal (Core.scalar u) Core.signatureR]

theorem verifyCompute_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : VerifyValues) {qb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator data.generator)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue data.publicValue)
    (hqb : OperandBytes s0 L.base usedBytes ⟨.input .q, .qLen⟩ qb)
    (hr : OperandBytes s0 L.base usedBytes Core.signatureR data.signatureR)
    (hs : OperandBytes s0 L.base usedBytes Core.signatureS data.signatureS)
    (hz : OperandBytes s0 L.base usedBytes Core.digest data.digest)
    (hgl : data.generator.length = L.pLen) (hyl : data.publicValue.length = L.pLen)
    (hqlen : qb.length = L.qLen) (hrl : data.signatureR.length = L.qLen) (hsl : data.signatureS.length = L.qLen)
    (hzl : data.digest.length < 2 ^ 64) (hqval : Spec.Dsa.decodeBE qb = L.subgroup)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (verifyCompute Sq.mm M.mm) s0 fun s5 =>
      Ready L s5 ∧ word s5.mem L.base Field.mask.offset = mask (verifyAccepted L data valid) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s5.mem ∧ Keep coreRegs s0 s5 := by
  obtain ⟨hql, hqu, _, _⟩ := L.widths
  have hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega
  unfold verifyCompute
  refine WP.seq (WP.mono (publicKey_ok M Sq h0 hp hq hop hoq hpf hqf hg hy hqb hgl hyl hqlen hqval hm)
    fun s1 ⟨h1, hm1, hqm1, hf1, hk1⟩ => ?_)
  have hg1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.generator]) hg
  have hy1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.publicValue]) hy
  have hr1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.signatureR]) hr
  have hs1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by trivial) hs
  have hz1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.digest]) hz
  refine WP.seq (WP.mono (readyRange_ok h1 .q Core.signatureR (by trivial) hr1.active
    (by rw [hrl]; omega) (by simp only [hrl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm1) fun s2 h2 => ?_)
  have hg2 := h2.preserve h1 (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  have hy2 := h2.preserve h1 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy1
  have hr2 := h2.preserve h1 (by decide) (by decide) (by simp [stablePointer, Core.signatureR]) hr1
  have hs2 := h2.preserve h1 (by decide) (by decide) (by trivial) hs1
  have hz2 := h2.preserve h1 (by decide) (by decide) (by simp [stablePointer, Core.digest]) hz1
  have hqm2 := h2.preserve h1 (Nat.le_refl _) (by decide) (by trivial) hqm1
  refine WP.seq (WP.mono (readyRange_ok h2.ready .q Core.signatureS (by trivial) hs2.active
    (by rw [hsl]; omega) (by simp only [hsl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false h2.mask) fun s3 h3 => ?_)
  have hg3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg2
  have hy3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy2
  have hr3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.signatureR]) hr2
  have hs3 := h3.preserve h2.ready (by decide) (by decide) (by trivial) hs2
  have hz3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.digest]) hz2
  have hqm3 := h3.preserve h2.ready (Nat.le_refl _) (by decide) (by trivial) hqm2
  refine WP.seq (WP.mono (coreVerify_ok M Sq h3.ready hp hq hop hoq hpf hqf data hg3 hy3 hr3 hs3 hz3
    hgl hyl hrl hsl hzl hqm3) fun s4 ⟨h4, hu4bytes, hf4, hm4eq, hk4⟩ => ?_)
  have hr4 := h3.ready.preserveExternal h4 hf4 hk4 (by decide) (by simp [stablePointer, Core.signatureR]) hr3
  have hm4 := hm4eq.trans h3.mask
  have hu4 := h4.encodedLocal .q u (data.value L) (by decide) hu hu4bytes
  refine WP.mono (readyEqual_ok h4 (Core.scalar u) Core.signatureR
    (by change u < 2 ^ 31; decide) (by trivial) hu4 hr4.active
    (by simp only [encodeBE_length, ModulusSide.length, hrl])
    (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) false hm4) fun s5 h5 => ?_
  refine ⟨h5.ready, ?_, (((hf1.trans h2.scheduleFrame).trans h3.scheduleFrame).trans hf4).trans h5.scheduleFrame,
    ((((hk1.trans h2.keep).trans h3.keep).trans hk4).trans h5.keep).mono (by decide)⟩
  have hm5 := h5.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length, ModulusSide.value] at hm5
  exact hm5

end VG.Proof.Dsa.X86_64
