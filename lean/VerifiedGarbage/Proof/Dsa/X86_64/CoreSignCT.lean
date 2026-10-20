module
public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState

import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleReduceCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleAddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleReduceCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant time of the complete DSA signing arithmetic schedule -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def signInputs (p : SchedulePublic) : List (Operand × Nat) :=
  [(Core.generator, p.layout.pLen), (Core.nonce, p.layout.qLen),
    (Core.privateScalar, p.layout.qLen), (Core.digest, p.digestLen)]

theorem signInputs_stable (p : SchedulePublic) (a : Operand × Nat) (ha : a ∈ signInputs p) :
    a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [signInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> simp [stablePointer, Core.generator, Core.nonce, Core.privateScalar, Core.digest]

theorem coreSignSchedule_ct (M : Mont) (Sq : MontS) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (members : ∀ p a, a ∈ signInputs p → a ∈ inputs p) :
    RelCT isa (Two (ScheduleState inputs)) (Core.sign Sq.mm M.mm)
      (Two (ScheduleState inputs)) := by
  have qp (p : SchedulePublic) : 1 ≤ p.layout.qLen := p.layout.widths.1
  have pp (p : SchedulePublic) : 1 ≤ p.layout.pLen := by have := p.layout.widths; omega
  have qb (p : SchedulePublic) : p.layout.qLen ≤ 1024 := by have := p.layout.widths; omega
  have hpfit (p : SchedulePublic) : (p.layout.pLen + 7) / 8 ≤ ModulusSide.p.words p.layout := Nat.le_refl _
  have hqfit (p : SchedulePublic) : (p.layout.qLen + 7) / 8 ≤ ModulusSide.q.words p.layout := Nat.le_refl _
  have h1 := schedulePow_ct M Sq inputs stable .p t Core.generator Core.nonce
    (fun p => p.layout.pLen) (fun p => p.layout.qLen) (by simp [pointerFits, Core.generator]) (by simp [pointerFits, Core.nonce]) (by simp [stablePointer, Core.generator]) (by simp [stablePointer, Core.nonce])
    pp hpfit qp qb (by decide) (by decide) (element_space (by decide)) (by taint_decide)
  have h2 := scheduleReduce_ct M inputs stable r (Core.element t) (fun p => p.layout.pLen)
    (by change t < 2 ^ 31; decide) (by simp [stablePointer, Core.element])
    (by intro p; have := p.layout.widths; omega)
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide)
  have h3 := schedulePow_ct M Sq inputs stable .q inverse Core.nonce (Core.scalar qMinusTwo)
    (fun p => p.layout.qLen) (fun p => p.layout.qLen) (by simp [pointerFits, Core.nonce]) (by change qMinusTwo < 2 ^ 31; decide)
    (by simp [stablePointer, Core.nonce]) (by simp [stablePointer, Core.scalar]) qp hqfit qp qb (by decide) (by decide) (scalar_space (by decide)) (by taint_decide)
  have h4 := scheduleProduct_ct M inputs stable .q u Core.privateScalar (Core.scalar r)
    (fun p => p.layout.qLen) (fun p => p.layout.qLen) (by simp [pointerFits, Core.privateScalar]) (by change r < 2 ^ 31; decide)
    (by simp [stablePointer, Core.privateScalar]) (by simp [stablePointer, Core.scalar]) qp hqfit qp hqfit (by decide) (by decide) (scalar_space (by decide)) (by taint_decide)
  have h5 := scheduleReduceKeep_ct M inputs stable z u Core.digest (fun p => p.digestLen)
    (by simp [pointerFits, Core.digest]) (by simp [stablePointer, Core.digest]) (fun p => p.digestBound) (by decide) (by decide) (scalar_space (by decide))
    (by decide) (scalar_space (by decide)) (by intro p; left; have := p.layout.widths; unfold u z; omega)
    (by taint_decide)
  have h6 := scheduleScalarAdd_ct inputs stable z u v
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (scalar_space (by decide)) (scalar_space (by decide)) (scalar_space (by decide)) (by taint_decide)
  have h7 := scheduleProduct_ct M inputs stable .q s (Core.scalar inverse) (Core.scalar v)
    (fun p => p.layout.qLen) (fun p => p.layout.qLen)
    (by change inverse < 2 ^ 31; decide) (by change v < 2 ^ 31; decide)
    (by simp [stablePointer, Core.scalar]) (by simp [stablePointer, Core.scalar]) qp hqfit qp hqfit (by decide) (by decide) (scalar_space (by decide)) (by taint_decide)
  unfold Core.sign seqs
  refine RelCT.seq (two_map (Φ := ScheduleState inputs) (fun p => p) (fun p st h =>
    ⟨h, (h.2.1 (Core.generator, p.layout.pLen) (members p _ (by simp [signInputs]))).active,
      (h.2.1 (Core.nonce, p.layout.qLen) (members p _ (by simp [signInputs]))).active⟩) h1) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h.1, h.1.1.availableLocal .p t (by decide) (element_space (by decide) p)⟩) h2) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h.1, (h.1.2.1 (Core.nonce, p.layout.qLen) (members p _ (by simp [signInputs]))).active,
      h.1.1.availableLocal .q qMinusTwo (by decide) (scalar_space (by decide) p)⟩) h3) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h.1, (h.1.2.1 (Core.privateScalar, p.layout.qLen) (members p _ (by simp [signInputs]))).active,
      h.1.1.availableLocal .q r (by decide) (scalar_space (by decide) p)⟩) h4) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨⟨h.1, (h.1.2.1 (Core.digest, p.digestLen) (members p _ (by simp [signInputs]))).active⟩, h.2⟩) h5) ?_
  refine RelCT.seq h6 ?_
  exact (two_map (fun p => p) (fun p st h =>
    ⟨h.1, h.1.1.availableLocal .q inverse (by decide) (scalar_space (by decide) p),
      h.1.1.availableLocal .q v (by decide) (scalar_space (by decide) p)⟩) h7).mono
    (fun _ _ h => h) (fun _ _ => two_mono (fun _ _ h => h.1))

theorem coreSign_ct (M : Mont) (Sq : MontS) : RelCT isa (Two (ScheduleState signInputs))
    (Core.sign Sq.mm M.mm) (fun _ _ => True) :=
  (coreSignSchedule_ct M Sq signInputs signInputs_stable (fun _ _ h => h)).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)

end VG.Proof.Dsa.X86_64
