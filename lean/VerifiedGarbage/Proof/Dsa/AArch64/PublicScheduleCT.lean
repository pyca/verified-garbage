module
public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeadCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState

import VerifiedGarbage.Proof.Dsa.AArch64.PublicFinishCT
import VerifiedGarbage.Proof.Dsa.AArch64.PublicPrefix
import VerifiedGarbage.Proof.Dsa.AArch64.PublicCalls
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallHeadCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicFinishCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicPrefix
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicCalls
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant time of DSA domain and public-key validation -/

/-! # Preserving the public subgroup order through DSA validation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- The input q is the public subgroup order, including its allocated width. -/
def PublicKeyPre (inputs : SchedulePublic → List (Operand × Nat)) (p : SchedulePublic) (s : State) : Prop :=
  ScheduleState inputs p s ∧ ∃ qb : List Byte,
    OperandBytes s p.layout.base usedBytes ⟨.input .q, .qLen⟩ qb ∧
    qb.length = p.layout.qLen ∧ Spec.Dsa.decodeBE qb = p.layout.subgroup

theorem publicPrefix_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p) :
    RelCT isa (Two (ScheduleState inputs)) (seqs (Checks.publicPrefix M.mm)) (Two (ScheduleState inputs)) := by
  have pp (p : SchedulePublic) : 1 ≤ p.layout.pLen := by have := p.layout.widths; omega
  have qp (p : SchedulePublic) : 1 ≤ p.layout.qLen := p.layout.widths.1
  have pf (p : SchedulePublic) : (p.layout.pLen + 7) / 8 ≤ ModulusSide.p.words p.layout := Nat.le_refl _
  have h1 := scheduleRange_ct inputs stable .p Core.generator (fun p => p.layout.pLen) true
    (by simp [pointerFits, Core.generator]) (by simp [stablePointer, Core.generator]) pp pf (by taint_decide)
  have h2 := scheduleRange_ct inputs stable .p Core.publicValue (fun p => p.layout.pLen) true
    (by simp [pointerFits, Core.publicValue]) (by simp [stablePointer, Core.publicValue]) pp pf (by taint_decide)
  have h3 := scheduleMinus_ct inputs stable .p 1 t (by decide)
    (fun p => Nat.le_of_lt p.pGreater) (by decide) (by decide) (element_space (by decide))
    (by taint_decide) (by taint_decide)
  have h4 := scheduleReduce_ct M inputs stable u (Core.element t) (fun p => p.layout.pLen)
    (by change t < 2 ^ 16; decide) (by simp [stablePointer, Core.element])
    (by intro p; have := p.layout.widths; omega)
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide)
  have h5 := scheduleZero_ct inputs stable (Core.scalar u) (fun p => p.layout.qLen) false
    (by change u < 2 ^ 16; decide) (by simp [stablePointer, Core.scalar]) (by decide)
    qp (by intro p; have := p.layout.widths; omega) (by taint_decide)
  have h6 := scheduleMinus_ct inputs stable .q 2 qMinusTwo (by decide)
    (by intro p; have := p.qGreater; change 2 ≤ p.layout.subgroup; omega)
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide) (by taint_decide)
  unfold Checks.publicPrefix seqs
  refine RelCT.seq (two_map (Φ := ScheduleState inputs) (fun p => p)
    (fun p st h => ⟨h, (h.2.1 _ (hg p)).active⟩) h1) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h => ⟨h, (h.2.1 _ (hy p)).active⟩) h2) ?_
  refine RelCT.seq h3 ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h, h.1.availableLocal .p t (by decide) (element_space (by decide) p)⟩) h4) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h.1, h.1.1.availableLocal .q u (by decide) (scalar_space (by decide) p)⟩) h5) ?_
  exact h6

theorem publicPrefix_known_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p) :
    RelCT isa (Two (PublicKeyPre inputs)) (seqs (Checks.publicPrefix M.mm)) (Two (PublicKeyPre inputs)) := by
  refine two_post (two_map (fun p => p) (fun _ _ h => h.1) ((publicPrefix_ct M inputs stable hg hy).mono (fun _ _ h => h) (fun _ _ _ => trivial))) ?_
  intro p s ⟨hs, qb, hqb, hql, hqv⟩
  obtain ⟨gb, hgb, hgl⟩ := hs.2.1 _ (hg p)
  obtain ⟨yb, hyb, hyl⟩ := hs.2.1 _ (hy p)
  obtain ⟨valid, hm⟩ := hs.2.2
  refine WP.mono (publicPrefix_ok M hs.1 p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits
    hgb hyb hqb hgl hyl hm) fun t ⟨hr, hmask, hq, hf, hk⟩ => ?_
  refine ⟨⟨hr, ?_, hmask⟩, qb, hq, hql, hqv⟩
  intro a ha
  obtain ⟨bs, hbs, hlen⟩ := hs.2.1 a ha
  exact ⟨bs, hs.1.preserveExternal hr hf hk (stable p a ha).1 (stable p a ha).2 hbs, hlen⟩

/-- The subgroup exponent's bytes are fixed by its public value and width. -/
theorem publicSubgroup_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (a : Operand) (ha : pointerFits a.pointer) (hpa : stablePointer a.pointer)
    (hin : ∀ p, (a, p.layout.pLen) ∈ inputs p)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (callHead a ⟨.input .q, .qLen⟩ (Core.element t) pWorkspace)) hc).isSome = true) :
    RelCT isa (Two (PublicKeyPre inputs))
      (Core.publicPow M.mm pWorkspace a ⟨.input .q, .qLen⟩ (Core.element t))
      (Two (PublicKeyPre inputs)) := by
  let pub (p : SchedulePublic) : ReadyCallPublic .p t :=
    scheduleCallPublic .p t (fun p => p.layout.pLen) (fun p => p.layout.qLen)
      (by intro p; have := p.layout.widths; omega) (fun _ => Nat.le_refl _)
      (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega)
      (by decide) (element_space (by decide)) p
  refine two_post (two_map (fun p => (pub p, Spec.Dsa.encodeBE p.layout.qLen p.layout.subgroup)) ?_
    (PublicPower.readyPublicPow_ct M .p t a ⟨.input .q, .qLen⟩ ha (by trivial) hpa (by change Field.q ≠ .mask; decide) (by decide) hT)) ?_
  · intro p s ⟨hs, qb, hqb, hql, hqv⟩
    obtain ⟨ab, hab, hal⟩ := hs.2.1 _ (hin p)
    have he : Spec.Dsa.encodeBE p.layout.qLen p.layout.subgroup = qb := by
      rw [← hql, ← hqv, VG.Proof.Dsa.encodeBE_decodeBE]
    rw [he]
    exact ⟨⟨hs.1, ab, qb, hab.active, hqb.active, hal, hql⟩, hqb.active, hql⟩
  · intro p s ⟨hs, qb, hqb, hql, hqv⟩
    obtain ⟨ab, hab, hal⟩ := hs.2.1 _ (hin p)
    refine WP.mono (readyPublicPow_ok M hs.1 .p p.pGreater p.pOdd a ⟨.input .q, .qLen⟩ ha (by trivial)
      hab.active hqb.active (by rw [hal]; have := p.layout.widths; omega)
      (by rw [hal]; exact Nat.le_refl _) (by rw [hql]; exact p.layout.widths.1)
      (by rw [hql]; have := p.layout.widths; omega) t (by decide) (element_space (by decide) p))
      fun s' h => ⟨h.schedule hs (by decide) (element_space (by decide) p) (stable p),
        qb, h.external (by decide) (element_space (by decide) p) hqb, hql, hqv⟩

theorem publicIsOne_ct (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer) :
    RelCT isa (Two (PublicKeyPre inputs)) (Checks.isOne pWorkspace (Core.element t))
      (Two (PublicKeyPre inputs)) := by
  have ct := scheduleIsOne_ct inputs stable .p (Core.element t) (fun p => p.layout.pLen)
    (by change t < 2 ^ 16; decide) (by trivial) (by intro p; have := p.layout.widths; omega)
    (fun _ => Nat.le_refl _) (by taint_decide)
  refine two_post (two_map (fun p => p) (fun p s h =>
    ⟨h.1, h.1.1.availableLocal .p t (by decide) (element_space (by decide) p)⟩) (ct.mono (fun _ _ h => h) (fun _ _ _ => trivial))) ?_
  intro p s ⟨hs, qb, hqb, hql, hqv⟩
  obtain ⟨valid, hm⟩ := hs.2.2
  have hb := hs.1.readLocal .p t (by decide) (element_space (by decide) p)
  have hl : (Spec.Rsa.bytesAt s.mem (off p.layout.base t) p.layout.pLen).length = p.layout.pLen := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  refine WP.mono (readyIsOne_ok hs.1 .p (Core.element t) (by change t < 2 ^ 16; decide) hb
    (by simp only [ModulusSide.length]; rw [hl]; have := p.layout.widths; omega) (by simp only [ModulusSide.length]; rw [hl]; exact Nat.le_refl _) hm)
    fun s' h => ⟨h.schedule hs (stable p), qb,
      h.preserve hs.1 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb, hql, hqv⟩

end VG.Proof.Dsa.AArch64
