module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Modulus
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyJoint
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Correctness of the complete six-operation DSA verification core -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure VerifyValues where
  generator : List Byte
  publicValue : List Byte
  signatureR : List Byte
  signatureS : List Byte
  digest : List Byte

def VerifyValues.value (L : ExecutionLayout) (data : VerifyValues) : Nat :=
  let ki := Spec.Dsa.powMod (Spec.Dsa.decodeBE data.signatureS) (L.subgroup - 2) L.subgroup
  let uu := (Spec.Dsa.decodeBE data.digest % L.subgroup) * ki % L.subgroup
  let vv := Spec.Dsa.decodeBE data.signatureR * ki % L.subgroup
  (Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) uu L.modulus *
    Spec.Dsa.powMod (Spec.Dsa.decodeBE data.publicValue) vv L.modulus % L.modulus) % L.subgroup

/-- All verification arithmetic runs for every signature; the entry point
combines the final equality with its accumulated validity mask. -/
theorem coreVerify_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : VerifyValues)
    (hg : OperandBytes s0 L.base usedBytes Core.generator data.generator)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue data.publicValue)
    (hr : OperandBytes s0 L.base usedBytes Core.signatureR data.signatureR)
    (hs : OperandBytes s0 L.base usedBytes Core.signatureS data.signatureS)
    (hz : OperandBytes s0 L.base usedBytes Core.digest data.digest)
    (hgl : data.generator.length = L.pLen) (hyl : data.publicValue.length = L.pLen)
    (hrl : data.signatureR.length = L.qLen) (hsl : data.signatureS.length = L.qLen)
    (hzl : data.digest.length < 2 ^ 64)
    (hqm : OperandBytes s0 L.base activeBytes (Core.scalar qMinusTwo) (Spec.Dsa.encodeBE L.qLen (L.subgroup - 2))) :
    WP isa (Core.verify Sq.mm M.mm) s0 fun s8 =>
      Ready L s8 ∧
      Spec.Rsa.bytesAt s8.mem (off L.base u) L.qLen = Spec.Dsa.encodeBE L.qLen (data.value L) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s8.mem ∧
      word s8.mem L.base Field.mask.offset = word s0.mem L.base Field.mask.offset ∧ Keep coreRegs s0 s8 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  have fitq (n : Nat) (h : n < L.subgroup) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.qLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hqf)
  have fitp (n : Nat) (h : n < L.modulus) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.pLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hpf)
  let ki := Spec.Dsa.powMod (Spec.Dsa.decodeBE data.signatureS) (L.subgroup - 2) L.subgroup
  let zz := Spec.Dsa.decodeBE data.digest % L.subgroup
  let uu := zz * ki % L.subgroup
  let vv := Spec.Dsa.decodeBE data.signatureR * ki % L.subgroup
  let tt := Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) uu L.modulus
  let tt2 := Spec.Dsa.powMod (Spec.Dsa.decodeBE data.publicValue) vv L.modulus
  let prod := tt * tt2 % L.modulus
  have hki : ki < L.subgroup := VG.Proof.Dsa.powMod_lt _ _ (by omega)
  have hzz : zz < L.subgroup := Nat.mod_lt _ (by omega)
  have huu : uu < L.subgroup := Nat.mod_lt _ (by omega)
  have hvv : vv < L.subgroup := Nat.mod_lt _ (by omega)
  have hprod : prod < L.modulus := Nat.mod_lt _ (by omega)
  have ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega
  have hi : inverse + L.qLen ≤ usedBytes := by unfold inverse usedBytes; omega
  have hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega
  have hz' : z + L.qLen ≤ usedBytes := by unfold z usedBytes; omega
  have hv : v + L.qLen ≤ usedBytes := by unfold v usedBytes; omega
  have hqmLen := encodeBE_length L.qLen (L.subgroup - 2)
  unfold Core.verify
  have step1 := readyPow_ok M Sq h0 .q (by change 1 < L.subgroup; omega) hoq
    Core.signatureS (Core.scalar qMinusTwo) (by trivial) (by change qMinusTwo < 2 ^ 31; decide)
    hs.active hqm (by rw [hsl]; omega)
    (by simp only [hsl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hqmLen]; omega) (by rw [hqmLen]; omega) inverse (by decide) hi
  have step1' : WP isa (Core.pow Sq.mm M.mm qWorkspace Core.signatureS (Core.scalar qMinusTwo) (Core.scalar inverse)) s0
      (CallResult L .q inverse ki s0) := by
    simpa only [ki, Core.scalar, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value,
      fitq (L.subgroup - 2) (by omega)] using step1
  refine WP.seq (WP.mono step1' fun s1 h1 => ?_)
  have hg1 := h1.external (by decide) hi hg
  have hy1 := h1.external (by decide) hi hy
  have hr1 := h1.external (by decide) hi hr
  have hz1 := h1.external (by decide) hi hz
  refine WP.seq (WP.mono (readyReduce_ok M h1.ready hq hoq Core.digest (by trivial) hz1.active hzl z (by decide) hz') fun s2 h2 => ?_)
  have hg2 := h2.external (by decide) hz' hg1
  have hy2 := h2.external (by decide) hz' hy1
  have hr2 := h2.external (by decide) hz' hr1
  have hi2 := h2.local (by decide) hz' (h1.output (by decide) hi)
    (by simp only [encodeBE_length, ModulusSide.length]; exact hi)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold inverse z; omega))
  have step3 := readyProduct_ok M h2.ready .q (by change 1 < L.subgroup; omega) hoq
    (Core.scalar z) (Core.scalar inverse) (by change z < 2 ^ 31; decide) (by change inverse < 2 ^ 31; decide)
    (h2.output (by decide) hz') hi2
    (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _)
    (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _) u (by decide) hu
  have step3' : WP isa (Core.product M.mm qWorkspace (Core.scalar z) (Core.scalar inverse) (Core.scalar u)) s2
      (CallResult L .q u uu s2) := by
    simpa only [Core.scalar, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.length, ModulusSide.value,
      show Spec.Dsa.decodeBE data.digest % L.subgroup = zz from rfl, fitq _ hzz, fitq _ hki, uu] using step3
  refine WP.seq (WP.mono step3' fun s3 h3 => ?_)
  have hg3 := h3.external (by decide) hu hg2
  have hy3 := h3.external (by decide) hu hy2
  have hr3 := h3.external (by decide) hu hr2
  have hi3 := h3.local (by decide) hu hi2
    (by simp only [encodeBE_length, ModulusSide.length]; exact hi)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold inverse u; omega))
  have step4 := readyProduct_ok M h3.ready .q (by change 1 < L.subgroup; omega) hoq
    Core.signatureR (Core.scalar inverse) (by trivial) (by change inverse < 2 ^ 31; decide) hr3.active hi3
    (by rw [hrl]; omega) (by simp only [hrl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _) v (by decide) hv
  have step4' : WP isa (Core.product M.mm qWorkspace Core.signatureR (Core.scalar inverse) (Core.scalar v)) s3
      (CallResult L .q v vv s3) := by
    simpa only [Core.scalar, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.length, ModulusSide.value,
      fitq _ hki, vv] using step4
  refine WP.seq (WP.mono step4' fun s4 h4 => ?_)
  have hg4 := h4.external (by decide) hv hg3
  have hy4 := h4.external (by decide) hv hy3
  have hu4 := h4.local (by decide) hv (h3.output (by decide) hu)
    (by simp only [encodeBE_length, ModulusSide.length]; exact hu)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold u v; omega))
  have step5 := readyJoint_ok M Sq h4.ready hp hop Core.generator Core.publicValue
    (by trivial) (by trivial) hg4.active hy4.active
    (by rw [hgl]; omega) (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hyl]; omega) (by simp only [hyl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    hu4 (h4.output (by decide) hv) (encodeBE_length _ _) (encodeBE_length _ _) t (by decide) ht
  have step5' : WP isa (Core.joint Sq.mm M.mm pWorkspace Core.generator Core.publicValue (Core.element t)) s4
      (CallResult L .p t prod s4) := by
    simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.length, ModulusSide.value,
      fitq _ huu, fitq _ hvv, prod, tt, tt2] using step5
  refine WP.seq (WP.mono step5' fun s7 h7 => ?_)
  have step8 := readyReduce_ok M h7.ready hq hoq (Core.element t) (by change t < 2 ^ 31; decide)
    (h7.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega) u (by decide) hu
  have step8' : WP isa (Core.reduce M.mm (Core.element t) (Core.scalar u)) s7
      (CallResult L .q u (data.value L) s7) := by
    simpa only [ModulusSide.length, fitp _ hprod, prod, tt, tt2, uu, vv, zz, ki, VerifyValues.value] using step8
  refine WP.mono step8' fun s8 h8 => ⟨h8.ready, h8.bytes, ?_, ?_, ?_⟩
  · exact (((((h1.scheduleFrame (by decide) hi).trans (h2.scheduleFrame (by decide) hz')).trans
      (h3.scheduleFrame (by decide) hu)).trans (h4.scheduleFrame (by decide) hv)).trans
      (h7.scheduleFrame (by decide) ht)).trans (h8.scheduleFrame (by decide) hu)
  · exact (h8.fields (by decide) hu .mask).trans ((h7.fields (by decide) ht .mask).trans
      ((h4.fields (by decide) hv .mask).trans ((h3.fields (by decide) hu .mask).trans
      ((h2.fields (by decide) hz' .mask).trans (h1.fields (by decide) hi .mask)))))
  · exact (((((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep).trans h7.keep).trans h8.keep).mono (by decide)

end VG.Proof.Dsa.X86_64
