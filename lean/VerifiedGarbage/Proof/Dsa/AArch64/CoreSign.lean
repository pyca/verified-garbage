module
public import VerifiedGarbage.Proof.Dsa.AArch64.Modulus

import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # Correctness of the complete seven-operation DSA signing core -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure SignValues where
  generator : List Byte
  nonce : List Byte
  privateScalar : List Byte
  digest : List Byte

def SignValues.r (L : ExecutionLayout) (data : SignValues) : Nat :=
  Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) (Spec.Dsa.decodeBE data.nonce) L.modulus % L.subgroup

def SignValues.s (L : ExecutionLayout) (data : SignValues) : Nat :=
  Spec.Dsa.powMod (Spec.Dsa.decodeBE data.nonce) (L.subgroup - 2) L.subgroup *
    ((Spec.Dsa.decodeBE data.digest % L.subgroup + Spec.Dsa.decodeBE data.privateScalar * data.r L % L.subgroup) % L.subgroup) % L.subgroup

/-- Computes both signature scalars even for out-of-range secret inputs.
The entry point applies the range and nonzero masks afterwards. -/
theorem coreSign_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : SignValues)
    (hg : OperandBytes s0 L.base usedBytes Core.generator data.generator)
    (hn : OperandBytes s0 L.base usedBytes Core.nonce data.nonce)
    (hx : OperandBytes s0 L.base usedBytes Core.privateScalar data.privateScalar)
    (hz : OperandBytes s0 L.base usedBytes Core.digest data.digest)
    (hgl : data.generator.length = L.pLen) (hnl : data.nonce.length = L.qLen)
    (hxl : data.privateScalar.length = L.qLen) (hzl : data.digest.length < 2 ^ 64)
    (hqm : OperandBytes s0 L.base activeBytes (Core.scalar qMinusTwo) (Spec.Dsa.encodeBE L.qLen (L.subgroup - 2))) :
    WP isa (Core.sign M.mm) s0 fun s7 =>
      Ready L s7 ∧
      Spec.Rsa.bytesAt s7.mem (off L.base r) L.qLen = Spec.Dsa.encodeBE L.qLen (data.r L) ∧
      Spec.Rsa.bytesAt s7.mem (off L.base s) L.qLen = Spec.Dsa.encodeBE L.qLen (data.s L) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s7.mem ∧
      word s7.mem L.base Field.mask.offset = word s0.mem L.base Field.mask.offset ∧ Keep coreRegs s0 s7 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  have fitq (n : Nat) (h : n < L.subgroup) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.qLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hqf)
  have fitp (n : Nat) (h : n < L.modulus) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.pLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hpf)
  let rr := data.r L
  let ki := Spec.Dsa.powMod (Spec.Dsa.decodeBE data.nonce) (L.subgroup - 2) L.subgroup
  let xr := Spec.Dsa.decodeBE data.privateScalar * rr % L.subgroup
  let zz := Spec.Dsa.decodeBE data.digest % L.subgroup
  let vv := (zz + xr) % L.subgroup
  have hrr : rr < L.subgroup := Nat.mod_lt _ (by omega)
  have hki : ki < L.subgroup := VG.Proof.Dsa.powMod_lt _ _ (by omega)
  have hxr : xr < L.subgroup := Nat.mod_lt _ (by omega)
  have hzz : zz < L.subgroup := Nat.mod_lt _ (by omega)
  have hvv : vv < L.subgroup := Nat.mod_lt _ (by omega)
  have ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega
  have hr : r + L.qLen ≤ usedBytes := by unfold r usedBytes; omega
  have hi : inverse + L.qLen ≤ usedBytes := by unfold inverse usedBytes; omega
  have hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega
  have hz' : z + L.qLen ≤ usedBytes := by unfold z usedBytes; omega
  have hv : v + L.qLen ≤ usedBytes := by unfold v usedBytes; omega
  have hs : s + L.qLen ≤ usedBytes := by unfold s usedBytes; omega
  have hqmLen := encodeBE_length L.qLen (L.subgroup - 2)
  unfold Core.sign
  refine WP.seq (WP.mono (readyPow_ok M h0 .p hp hop Core.generator Core.nonce (by trivial) (by trivial)
    hg.active hn.active (by rw [hgl]; omega) (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hnl]; omega) (by rw [hnl]; omega) t (by decide) ht) fun s1 h1 => ?_)
  have hn1 := h1.external (by decide) ht hn
  have hx1 := h1.external (by decide) ht hx
  have hz1 := h1.external (by decide) ht hz
  have hqm1 := h1.local (by decide) ht hqm
    (by rw [hqmLen]; unfold qMinusTwo usedBytes; omega)
    (Or.inl (by rw [hqmLen]; unfold qMinusTwo t; omega))
  have step2 := readyReduce_ok M h1.ready hq hoq (Core.element t) (by change t < 2 ^ 16; decide)
    (h1.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega) r (by decide) hr
  have step2' : WP isa (Core.reduce M.mm (Core.element t) (Core.scalar r)) s1 (CallResult L .q r rr s1) := by
    simpa only [rr, SignValues.r, ModulusSide.length, ModulusSide.value, fitp _ (VG.Proof.Dsa.powMod_lt _ _ (by omega))] using step2
  refine WP.seq (WP.mono step2' fun s2 h2 => ?_)
  have hn2 := h2.external (by decide) hr hn1
  have hx2 := h2.external (by decide) hr hx1
  have hz2 := h2.external (by decide) hr hz1
  have hqm2 := h2.local (by decide) hr hqm1
    (by rw [hqmLen]; unfold qMinusTwo usedBytes; omega)
    (Or.inr (by simp only [ModulusSide.length]; unfold r qMinusTwo; omega))
  have step3 := readyPow_ok M h2.ready .q (by change 1 < L.subgroup; omega) hoq Core.nonce (Core.scalar qMinusTwo)
    (by trivial) (by change qMinusTwo < 2 ^ 16; decide) hn2.active hqm2 (by rw [hnl]; omega) (by simp only [hnl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hqmLen]; omega) (by rw [hqmLen]; omega) inverse (by decide) hi
  have step3' : WP isa (Core.pow M.mm qWorkspace Core.nonce (Core.scalar qMinusTwo) (Core.scalar inverse)) s2
      (CallResult L .q inverse ki s2) := by
    simpa only [ki, Core.scalar, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value, fitq (L.subgroup - 2) (by omega)] using step3
  refine WP.seq (WP.mono step3' fun s3 h3 => ?_)
  have hx3 := h3.external (by decide) hi hx2
  have hz3 := h3.external (by decide) hi hz2
  have hr3 := h3.local (by decide) hi (h2.output (by decide) hr)
    (by simp only [encodeBE_length, ModulusSide.length]; exact hr) (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold r inverse; omega))
  have step4 := readyProduct_ok M h3.ready .q (by change 1 < L.subgroup; omega) hoq Core.privateScalar (Core.scalar r)
    (by trivial) (by change r < 2 ^ 16; decide) hx3.active hr3 (by rw [hxl]; omega) (by simp only [hxl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _) u (by decide) hu
  have step4' : WP isa (Core.product M.mm qWorkspace Core.privateScalar (Core.scalar r) (Core.scalar u)) s3
      (CallResult L .q u xr s3) := by
    simpa only [xr, Core.scalar, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.length, ModulusSide.value, fitq _ hrr] using step4
  refine WP.seq (WP.mono step4' fun s4 h4 => ?_)
  have hz4 := h4.external (by decide) hu hz3
  have hr4 := h4.local (by decide) hu hr3 (by simp only [encodeBE_length, ModulusSide.length]; exact hr)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold r u; omega))
  have hi4 := h4.local (by decide) hu (h3.output (by decide) hi) (by simp only [encodeBE_length, ModulusSide.length]; exact hi)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold inverse u; omega))
  refine WP.seq (WP.mono (readyReduce_ok M h4.ready hq hoq Core.digest (by trivial) hz4.active hzl z (by decide) hz') fun s5 h5 => ?_)
  have hr5 := h5.local (by decide) hz' hr4 (by simp only [encodeBE_length, ModulusSide.length]; exact hr)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold r z; omega))
  have hi5 := h5.local (by decide) hz' hi4 (by simp only [encodeBE_length, ModulusSide.length]; exact hi)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold inverse z; omega))
  have hu5 := h5.local (by decide) hz' (h4.output (by decide) hu) (by simp only [encodeBE_length, ModulusSide.length]; exact hu)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold u z; omega))
  have step6 := readyAdd_ok h5.ready (Core.scalar z) (Core.scalar u) (by change z < 2 ^ 16; decide) (by change u < 2 ^ 16; decide)
    (h5.output (by decide) hz') hu5
    (by simp only [encodeBE_length, ModulusSide.length]; omega) (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _)
    (by simp only [ModulusSide.length]; rw [fitq _ hzz]; exact hzz) (by simp only [ModulusSide.length]; rw [fitq _ hxr]; exact hxr) v (by decide) hv
  have step6' : WP isa (Core.add (Core.scalar z) (Core.scalar u) (Core.scalar v)) s5
      (CallResult L .q v vv s5) := by
    simpa only [ModulusSide.length, show Spec.Dsa.decodeBE data.digest % L.subgroup = zz from rfl, fitq _ hzz, fitq _ hxr, vv] using step6
  refine WP.seq (WP.mono step6' fun s6 h6 => ?_)
  have hr6 := h6.local (by decide) hv hr5 (by simp only [encodeBE_length, ModulusSide.length]; exact hr)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold r v; omega))
  have hi6 := h6.local (by decide) hv hi5 (by simp only [encodeBE_length, ModulusSide.length]; exact hi)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold inverse v; omega))
  have step7 := readyProduct_ok M h6.ready .q (by change 1 < L.subgroup; omega) hoq (Core.scalar inverse) (Core.scalar v)
    (by change inverse < 2 ^ 16; decide) (by change v < 2 ^ 16; decide) hi6 (h6.output (by decide) hv)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _) s (by decide) hs
  have step7' : WP isa (Core.product M.mm qWorkspace (Core.scalar inverse) (Core.scalar v) (Core.scalar s)) s6
      (CallResult L .q s (data.s L) s6) := by
    simpa only [Core.scalar, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.length, ModulusSide.value, fitq _ hki, fitq _ hvv, ki, vv, zz, xr, rr, SignValues.s] using step7
  refine WP.mono step7' fun s7 h7 => ?_
  have hr7 := h7.local (by decide) hs hr6 (by simp only [encodeBE_length, ModulusSide.length]; exact hr)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold r s; omega))
  refine ⟨h7.ready, ?_, h7.bytes, ?_, ?_, ?_⟩
  · simpa only [encodeBE_length, ModulusSide.length, pointerValue, rr] using operand_bytesAt hr7
  · exact ((((((h1.scheduleFrame (by decide) ht).trans (h2.scheduleFrame (by decide) hr)).trans (h3.scheduleFrame (by decide) hi)).trans
      (h4.scheduleFrame (by decide) hu)).trans (h5.scheduleFrame (by decide) hz')).trans (h6.scheduleFrame (by decide) hv)).trans (h7.scheduleFrame (by decide) hs)
  · exact (h7.fields (by decide) hs .mask).trans ((h6.fields (by decide) hv .mask).trans ((h5.fields (by decide) hz' .mask).trans ((h4.fields (by decide) hu .mask).trans ((h3.fields (by decide) hi .mask).trans ((h2.fields (by decide) hr .mask).trans ((h1.fields (by decide) ht .mask)))))))
  · have k1 := h1.keep
    have k2 : Keep coreRegs s0 s2 := (k1.trans h2.keep).mono (by decide)
    have k3 : Keep coreRegs s0 s3 := (k2.trans h3.keep).mono (by decide)
    have k4 : Keep coreRegs s0 s4 := (k3.trans h4.keep).mono (by decide)
    have k5 : Keep coreRegs s0 s5 := (k4.trans h5.keep).mono (by decide)
    have k6 : Keep coreRegs s0 s6 := (k5.trans h6.keep).mono (by decide)
    have k7 : Keep coreRegs s0 s7 := (k6.trans h7.keep).mono (by decide)
    exact k7

end VG.Proof.Dsa.AArch64
