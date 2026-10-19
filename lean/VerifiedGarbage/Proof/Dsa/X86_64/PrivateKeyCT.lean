module
public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState

import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant time of private-key consistency and nonce validation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem privateKey_ct (M : Mont) (Sq : MontS) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p)
    (hx : ∀ p, (Core.privateScalar, p.layout.qLen) ∈ inputs p)
    (hk : ∀ p, (Core.nonce, p.layout.qLen) ∈ inputs p) :
    RelCT isa (Two (ScheduleState inputs)) (Checks.privateKey Sq.mm M.mm)
      (Two (ScheduleState inputs)) := by
  have pp (p : SchedulePublic) : 1 ≤ p.layout.pLen := by have := p.layout.widths; omega
  have qp (p : SchedulePublic) : 1 ≤ p.layout.qLen := p.layout.widths.1
  have qb (p : SchedulePublic) : p.layout.qLen ≤ 1024 := by have := p.layout.widths; omega
  have pf (p : SchedulePublic) : (p.layout.pLen + 7) / 8 ≤ ModulusSide.p.words p.layout := Nat.le_refl _
  have qf (p : SchedulePublic) : (p.layout.qLen + 7) / 8 ≤ ModulusSide.q.words p.layout := Nat.le_refl _
  have h1 := scheduleRange_ct inputs stable .q Core.privateScalar (fun p => p.layout.qLen) false
    (by simp [pointerFits, Core.privateScalar]) (by simp [stablePointer, Core.privateScalar]) qp qf (by taint_decide)
  have h2 := scheduleRange_ct inputs stable .q Core.nonce (fun p => p.layout.qLen) false
    (by simp [pointerFits, Core.nonce]) (by simp [stablePointer, Core.nonce]) qp qf (by taint_decide)
  have h3 := schedulePow_ct M Sq inputs stable .p t Core.generator Core.privateScalar
    (fun p => p.layout.pLen) (fun p => p.layout.qLen)
    (by simp [pointerFits, Core.generator]) (by simp [pointerFits, Core.privateScalar])
    (by simp [stablePointer, Core.generator]) (by simp [stablePointer, Core.privateScalar])
    pp pf qp qb (by decide) (by decide) (element_space (by decide)) (by taint_decide)
  have h4 := scheduleEqual_ct inputs stable (Core.element t) Core.publicValue (fun p => p.layout.pLen) false
    (by change t < 2 ^ 31; decide) (by simp [pointerFits, Core.publicValue])
    (by simp [stablePointer, Core.element]) (by simp [stablePointer, Core.publicValue]) (by decide)
    pp (by intro p; have := p.layout.widths; omega) (by taint_decide)
  unfold Checks.privateKey seqs
  refine RelCT.seq (two_map (Φ := ScheduleState inputs) (fun p => p)
    (fun p st h => ⟨h, (h.2.1 _ (hx p)).active⟩) h1) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h => ⟨h, (h.2.1 _ (hk p)).active⟩) h2) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h, (h.2.1 _ (hg p)).active, (h.2.1 _ (hx p)).active⟩) h3) ?_
  exact two_map (fun p => p) (fun p st h =>
    ⟨h.1, h.1.1.availableLocal .p t (by decide) (element_space (by decide) p),
      (h.1.2.1 _ (hy p)).active⟩) h4

end VG.Proof.Dsa.X86_64
