module
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState

import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleReduceCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleJointCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleReduceCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleJointCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant time of the complete DSA verification arithmetic schedule -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def verifyInputs (p : SchedulePublic) : List (Operand × Nat) :=
  [(Core.generator, p.layout.pLen), (Core.publicValue, p.layout.pLen),
    (Core.signatureR, p.layout.qLen), (Core.signatureS, p.layout.qLen), (Core.digest, p.digestLen)]

theorem verifyInputs_stable (p : SchedulePublic) (a : Operand × Nat) (ha : a ∈ verifyInputs p) :
    a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [verifyInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    simp [stablePointer, Core.generator, Core.publicValue, Core.signatureR, Core.signatureS, Core.digest]

theorem coreVerifySchedule_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (members : ∀ p a, a ∈ verifyInputs p → a ∈ inputs p) :
    RelCT isa (Two (ScheduleState inputs)) (Core.verify M.mm)
      (Two (ScheduleState inputs)) := by
  have qp (p : SchedulePublic) : 1 ≤ p.layout.qLen := p.layout.widths.1
  have pp (p : SchedulePublic) : 1 ≤ p.layout.pLen := by have := p.layout.widths; omega
  have qb (p : SchedulePublic) : p.layout.qLen ≤ 1024 := by have := p.layout.widths; omega
  have hpfit (p : SchedulePublic) : (p.layout.pLen + 7) / 8 ≤ ModulusSide.p.words p.layout := Nat.le_refl _
  have hqfit (p : SchedulePublic) : (p.layout.qLen + 7) / 8 ≤ ModulusSide.q.words p.layout := Nat.le_refl _
  have h1 := schedulePow_ct M inputs stable .q inverse Core.signatureS (Core.scalar qMinusTwo)
    (fun p => p.layout.qLen) (fun p => p.layout.qLen)
    (by trivial) (by change qMinusTwo < 2 ^ 16; decide) (by trivial) (by trivial)
    qp hqfit qp qb (by decide) (by decide) (scalar_space (by decide)) (by taint_decide)
  have h2 := scheduleReduce_ct M inputs stable z Core.digest (fun p => p.digestLen)
    (by trivial) (by simp [stablePointer, Core.digest]) (fun p => p.digestBound)
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide)
  have h3 := scheduleProduct_ct M inputs stable .q u (Core.scalar z) (Core.scalar inverse)
    (fun p => p.layout.qLen) (fun p => p.layout.qLen)
    (by change z < 2 ^ 16; decide) (by change inverse < 2 ^ 16; decide) (by trivial) (by trivial)
    qp hqfit qp hqfit (by decide) (by decide) (scalar_space (by decide)) (by taint_decide)
  have h4 := scheduleProduct_ct M inputs stable .q v Core.signatureR (Core.scalar inverse)
    (fun p => p.layout.qLen) (fun p => p.layout.qLen)
    (by trivial) (by change inverse < 2 ^ 16; decide) (by simp [stablePointer, Core.signatureR]) (by trivial)
    qp hqfit qp hqfit (by decide) (by decide) (scalar_space (by decide)) (by taint_decide)
  have h5 := scheduleJoint_ct M inputs stable t Core.generator Core.publicValue
    (fun p => p.layout.pLen) (fun p => p.layout.pLen)
    (by trivial) (by trivial) (by simp [stablePointer, Core.generator]) (by simp [stablePointer, Core.publicValue])
    pp hpfit pp hpfit (by decide) (by decide) (element_space (by decide)) (by taint_decide)
  have h8 := scheduleReduce_ct M inputs stable u (Core.element t) (fun p => p.layout.pLen)
    (by change t < 2 ^ 16; decide) (by trivial) (by intro p; have := p.layout.widths; omega)
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide)
  unfold Core.verify seqs
  refine RelCT.seq (two_map (Φ := ScheduleState inputs) (fun p => p) (fun p st h =>
    ⟨h, (h.2.1 (Core.signatureS, p.layout.qLen) (members p _ (by simp [verifyInputs]))).active,
      h.1.availableLocal .q qMinusTwo (by decide) (scalar_space (by decide) p)⟩) h1) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h.1, (h.1.2.1 (Core.digest, p.digestLen) (members p _ (by simp [verifyInputs]))).active⟩) h2) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h.1, h.1.1.availableLocal .q z (by decide) (scalar_space (by decide) p),
      h.1.1.availableLocal .q inverse (by decide) (scalar_space (by decide) p)⟩) h3) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h.1, (h.1.2.1 (Core.signatureR, p.layout.qLen) (members p _ (by simp [verifyInputs]))).active,
      h.1.1.availableLocal .q inverse (by decide) (scalar_space (by decide) p)⟩) h4) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h.1, (h.1.2.1 (Core.generator, p.layout.pLen) (members p _ (by simp [verifyInputs]))).active,
      (h.1.2.1 (Core.publicValue, p.layout.pLen) (members p _ (by simp [verifyInputs]))).active⟩) h5) ?_
  exact (two_map (fun p => p) (fun p st h =>
    ⟨h.1, h.1.1.availableLocal .p t (by decide) (element_space (by decide) p)⟩) h8).mono
    (fun _ _ h => h) (fun _ _ => two_mono (fun _ _ h => h.1))

theorem coreVerify_ct (M : Mont) : RelCT isa (Two (ScheduleState verifyInputs))
    (Core.verify M.mm) (fun _ _ => True) :=
  (coreVerifySchedule_ct M verifyInputs verifyInputs_stable (fun _ _ h => h)).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)

end VG.Proof.Dsa.AArch64
