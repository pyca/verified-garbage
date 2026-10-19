module
public import VerifiedGarbage.Proof.Dsa.X86_64.Derive
public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState

import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.DeriveCopy
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Derive
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.DeriveCopy
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT

/-! # Constant time of derivation's computation: x's range, g^x, y's copy and the key checks

The operands' bytes may differ between two calls, x's among them: the
schedule relates two runs by their public layout alone. The subgroup order's
bytes are kept exactly, at derivation's extent, for the key checks. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Derivation's operands: y's slot, q, g and x. -/
def deriveInputs (p : SchedulePublic) : List (Operand × Nat) :=
  [(Core.publicValue, p.layout.pLen), (⟨.input .q, .qLen⟩, p.layout.qLen), (Core.generator, p.layout.pLen),
    (Core.privateScalar, p.layout.qLen)]

theorem deriveInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ deriveInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [deriveInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · simp [Core.publicValue, stablePointer]
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · simp [Core.generator, stablePointer]
  · simp [Core.privateScalar, stablePointer]

/-- An operand past the signer's layout stays available, with whatever bytes
it then holds, when its pointer and length do. -/
theorem ExternalAvailable.rebuild {L : ExecutionLayout} {a : Operand} {n : Nat} {s t : State}
    (hs : Ready L s) (ht : Ready L t) (hk : Keep coreRegs s t)
    (ha : a.length ≠ .mask) (hp : stablePointer a.pointer)
    (h : ExternalAvailable L a n s) : ExternalAvailable L a n t := by
  obtain ⟨bs, hb, hl⟩ := h
  have hptr := hs.pointer_eq ht a.pointer hp
  refine ⟨Spec.Rsa.bytesAt t.mem (pointerValue t.mem L.base a.pointer) n, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [bytesAt_length]
    exact (ht.fields a.length ha).trans ((hs.fields a.length ha).symm.trans (hl ▸ hb.length))
  · intro i hi
    rw [bytesAt_length] at hi
    rw [hk.2.1, hk.2.2, hptr]
    exact hb.source.rd i (by omega)
  · intro i hi
    simp [Spec.Rsa.bytesAt]
  · intro i hi
    rw [bytesAt_length] at hi
    rw [hptr]
    exact hb.source.out i (by omega)
  · exact bytesAt_length _ _ _

/-- The schedule's state, with derivation's extent and q's bytes. -/
def DeriveSched (p : SchedulePublic) (s : State) : Prop :=
  ScheduleState deriveInputs p s ∧ Scr s p.layout.base deriveExtent ∧
  ∃ qb : List Byte, OperandBytes s p.layout.base deriveExtent ⟨.input .q, .qLen⟩ qb ∧
    qb.length = p.layout.qLen ∧ Spec.Dsa.decodeBE qb = p.layout.subgroup

theorem deriveRange_ct : RelCT isa (Two DeriveSched) (Checks.range qWorkspace Core.privateScalar)
    (Two DeriveSched) := by
  have ct := scheduleRange_ct deriveInputs (fun p => deriveInputs_stable p) .q Core.privateScalar
    (fun p => p.layout.qLen) false (by trivial) (by simp [stablePointer, Core.privateScalar])
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  refine two_post ((two_map (fun p => p) (fun p s h => ⟨h.1, (h.1.2.1 (Core.privateScalar, p.layout.qLen)
    (by simp [deriveInputs])).active⟩)
    ct).mono (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro p s ⟨hs, hscr, qb, hqb, hql, hqv⟩
  obtain ⟨bs, hbs, hlen⟩ := hs.2.1 _ (show (Core.privateScalar, p.layout.qLen) ∈ deriveInputs p by
    simp [deriveInputs])
  obtain ⟨valid, hm⟩ := hs.2.2
  refine WP.mono (readyRange_ok hs.1 .q Core.privateScalar (by trivial) hbs.active
    (by rw [hlen]; exact p.layout.widths.1) (by rw [hlen]; exact Nat.le_refl _) false hm) fun t h => ?_
  exact ⟨h.schedule hs (fun a ha => deriveInputs_stable p a ha), hscr.congr h.keep.2.2,
    qb, h.preserve hs.1 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb, hql, hqv⟩

theorem derivePow_ct (M : Mont) (Sq : MontS) : RelCT isa (Two DeriveSched)
    (Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2)) (Two DeriveSched) := by
  have hend (p : SchedulePublic) : t2 + ModulusSide.p.length p.layout ≤ usedBytes := element_space (by decide) p
  have ct := schedulePow_ct M Sq deriveInputs (fun p => deriveInputs_stable p) .p t2 Core.generator
    Core.privateScalar (fun p => p.layout.pLen) (fun p => p.layout.qLen) (by trivial) (by trivial)
    (by simp [stablePointer, Core.generator]) (by simp [stablePointer, Core.privateScalar])
    (by intro p; have := p.layout.widths; omega) (fun _ => Nat.le_refl _)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega)
    (by decide) (by decide) hend (by taint_decide)
  refine two_post ((two_map (fun p => p) (fun p s h => ⟨h.1,
    (h.1.2.1 (Core.generator, p.layout.pLen) (by simp [deriveInputs])).active,
    (h.1.2.1 (Core.privateScalar, p.layout.qLen) (by simp [deriveInputs])).active⟩) ct).mono (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro p s ⟨hs, hscr, qb, hqb, hql, hqv⟩
  obtain ⟨ga, hga, hgl⟩ := hs.2.1 _ (show (Core.generator, p.layout.pLen) ∈ deriveInputs p by
    simp [deriveInputs])
  obtain ⟨xa, hxa, hxl⟩ := hs.2.1 _ (show (Core.privateScalar, p.layout.qLen) ∈ deriveInputs p by
    simp [deriveInputs])
  have step := readyPow_ok M Sq hs.1 .p (p.greater .p) (p.odd .p) Core.generator Core.privateScalar
    (by trivial) (by trivial) hga.active hxa.active (by rw [hgl]; have := p.layout.widths; omega)
    (by rw [hgl]; exact Nat.le_refl _) (by rw [hxl]; exact p.layout.widths.1)
    (by rw [hxl]; have := p.layout.widths; omega) t2 (by decide) (hend p)
  refine WP.mono (by simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField] using step)
    fun t h => ?_
  have hf : Outside p.layout.base 128 (deriveExtent - 128) s.mem t.mem :=
    (h.scheduleFrame (by decide) (hend p)).mono (by decide) (by decide)
  exact ⟨h.schedule hs (by decide) (hend p) (fun a ha => deriveInputs_stable p a ha), hscr.congr h.keep.2.2,
    qb, hqb.frame hs.1 h.ready hf h.keep (by decide) (by change Field.q ≠ .mask; decide), hql, hqv⟩

def CopyRegs (p : SchedulePublic) (s : State) : Prop :=
  s.gpr .rsi = off p.layout.base t2 ∧ s.gpr .rdx = off p.layout.base derivedY ∧
    s.gpr .rcx = BitVec.ofNat 64 p.layout.pLen

theorem deriveCopy_ct : RelCT isa (Two DeriveSched) Generate.copyY (Two DeriveSched) := by
  have ct : RelCT isa (Two DeriveSched) Generate.copyY (fun _ _ => True) := by
    unfold Generate.copyY seqs
    refine RelCT.seq (two_piece (Ψ := CopyRegs) [.rdi]
      (pins_of (fun p _ => p.layout.base) (by
        intro p s h r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact h.1.1.parent.rdi)) (by taint_decide) ?_) ?_
    · intro p s h
      exact WP.mono (copyHead_ok h.1.1) fun t ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3⟩
    · exact two_taint [.rsi, .rdx, .rcx]
        (pins_of (fun p r => if r = .rsi then off p.layout.base t2 else if r = .rdx then off p.layout.base derivedY
            else BitVec.ofNat 64 p.layout.pLen)
          (by
            intro p s h r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact h.1
            · exact h.2.1
            · exact h.2.2)) (by taint_decide)
  refine two_post ct ?_
  intro p s ⟨hs, hscr, qb, hqb, hql, hqv⟩
  refine WP.mono (copyY_ok hs.1 hscr) fun t ⟨ht, _, hf, hk⟩ => ?_
  have hp384 : p.layout.pLen ≤ 384 := p.layout.widths.2.2.2
  have hf' : Outside p.layout.base 128 (deriveExtent - 128) s.mem t.mem :=
    hf.mono (by decide) (by unfold deriveExtent; omega_using [hp384])
  obtain ⟨valid, hm⟩ := hs.2.2
  refine ⟨⟨ht, fun a ha => (hs.2.1 a ha).rebuild hs.1 ht hk (deriveInputs_stable p a ha).1
    (deriveInputs_stable p a ha).2, valid, (hf.word (Or.inl (by decide)) (by decide)).trans hm⟩,
    hscr.congr hk.2.2, qb, hqb.frame hs.1 ht hf' hk (by decide) (by change Field.q ≠ .mask; decide), hql, hqv⟩

theorem deriveBodySched_ct (M : Mont) (Sq : MontS) : RelCT isa (Two DeriveSched)
    (seqs [Checks.range qWorkspace Core.privateScalar,
      Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, Checks.signingKey Sq.mm M.mm]) (fun _ _ => True) := by
  have h4 := signingKey_ct M Sq deriveInputs (fun p => deriveInputs_stable p)
    (by intro p; simp [deriveInputs]) (by intro p; simp [deriveInputs]) (by intro p; simp [deriveInputs])
  unfold seqs
  refine RelCT.seq deriveRange_ct (RelCT.seq (derivePow_ct M Sq) (RelCT.seq deriveCopy_ct ?_))
  refine (two_map (Φ := DeriveSched) (fun p => p) (fun p s h => ⟨h.1, ?_⟩) h4).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)
  obtain ⟨qb, hqb, hql, hqv⟩ := h.2.2
  exact ⟨qb, hqb.shrink (by decide), hql, hqv⟩

end VG.Proof.Dsa.X86_64
