module

public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-! # Constant time of DSA domain and public-key validation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem publicKey_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p)
    (hq : ∀ p, (⟨.input .q, .qLen⟩, p.layout.qLen) ∈ inputs p) :
    RelCT isa (Two (ScheduleState inputs)) (Checks.publicKey M.mm)
      (Two (ScheduleState inputs)) := by
  have pp (p : SchedulePublic) : 1 ≤ p.layout.pLen := by have := p.layout.widths; omega
  have qp (p : SchedulePublic) : 1 ≤ p.layout.qLen := p.layout.widths.1
  have qb (p : SchedulePublic) : p.layout.qLen ≤ 1024 := by have := p.layout.widths; omega
  have pf (p : SchedulePublic) : (p.layout.pLen + 7) / 8 ≤ ModulusSide.p.words p.layout := Nat.le_refl _
  have h1 := scheduleRange_ct inputs stable .p Core.generator (fun p => p.layout.pLen) true
    (by simp [pointerFits, Core.generator]) (by simp [stablePointer, Core.generator]) pp pf (by taint_decide)
  have h2 := scheduleRange_ct inputs stable .p Core.publicValue (fun p => p.layout.pLen) true
    (by simp [pointerFits, Core.publicValue]) (by simp [stablePointer, Core.publicValue]) pp pf (by taint_decide)
  have h3 := scheduleMinus_ct inputs stable .p 1 t (by decide)
    (fun p => Nat.le_of_lt p.pGreater) (by decide) (by decide) (element_space (by decide))
    (by taint_decide) (by taint_decide)
  have h4 := scheduleReduce_ct M inputs stable u (Core.element t) (fun p => p.layout.pLen)
    (by change t < 2 ^ 31; decide) (by simp [stablePointer, Core.element])
    (by intro p; have := p.layout.widths; omega)
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide)
  have h5 := scheduleZero_ct inputs stable (Core.scalar u) (fun p => p.layout.qLen) false
    (by change u < 2 ^ 31; decide) (by simp [stablePointer, Core.scalar]) (by decide)
    qp (by intro p; have := p.layout.widths; omega) (by taint_decide)
  have h6 := scheduleMinus_ct inputs stable .q 2 qMinusTwo (by decide)
    (by intro p; have := p.qGreater; change 2 ≤ p.layout.subgroup; omega)
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide) (by taint_decide)
  have h7 := schedulePow_ct M inputs stable .p t Core.generator ⟨.input .q, .qLen⟩
    (fun p => p.layout.pLen) (fun p => p.layout.qLen)
    (by simp [pointerFits, Core.generator]) (by trivial)
    (by simp [stablePointer, Core.generator]) (by change Field.q ≠ .mask; decide)
    pp pf qp qb (by decide) (by decide) (element_space (by decide)) (by taint_decide)
  have h8 := scheduleIsOne_ct inputs stable .p (Core.element t) (fun p => p.layout.pLen)
    (by change t < 2 ^ 31; decide) (by simp [stablePointer, Core.element]) pp pf (by taint_decide)
  have h9 := schedulePow_ct M inputs stable .p t Core.publicValue ⟨.input .q, .qLen⟩
    (fun p => p.layout.pLen) (fun p => p.layout.qLen)
    (by simp [pointerFits, Core.publicValue]) (by trivial)
    (by simp [stablePointer, Core.publicValue]) (by change Field.q ≠ .mask; decide)
    pp pf qp qb (by decide) (by decide) (element_space (by decide)) (by taint_decide)
  unfold Checks.publicKey seqs
  refine RelCT.seq (two_map (Φ := ScheduleState inputs) (fun p => p)
    (fun p st h => ⟨h, (h.2.1 _ (hg p)).active⟩) h1) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h => ⟨h, (h.2.1 _ (hy p)).active⟩) h2) ?_
  refine RelCT.seq h3 ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h, h.1.availableLocal .p t (by decide) (element_space (by decide) p)⟩) h4) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h.1, h.1.1.availableLocal .q u (by decide) (scalar_space (by decide) p)⟩) h5) ?_
  refine RelCT.seq h6 ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h, (h.2.1 _ (hg p)).active, (h.2.1 _ (hq p)).active⟩) h7) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h.1, h.1.1.availableLocal .p t (by decide) (element_space (by decide) p)⟩) h8) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h, (h.2.1 _ (hy p)).active, (h.2.1 _ (hq p)).active⟩) h9) ?_
  exact two_map (fun p => p) (fun p st h =>
    ⟨h.1, h.1.1.availableLocal .p t (by decide) (element_space (by decide) p)⟩) h8

end VG.Proof.Dsa.X86_64
