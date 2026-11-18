module

import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.X86_64.CallHeadCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
import VerifiedGarbage.Proof.Dsa.X86_64.PublicFinishCT
import VerifiedGarbage.Proof.Dsa.X86_64.PublicCalls
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.X86_64.CallHeadCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicFinishCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicCalls
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
import VerifiedGarbage.Proof.Dsa.Zero
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
meta import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! ### `Dsa.X86_64.PublicScheduleCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.PublicPrefix`, which only this module used -/

section

/-! # DSA validation before the public subgroup exponentiations -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem publicPrefix_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb yb qb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator gb)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hqb : OperandBytes s0 L.base usedBytes ⟨.input .q, .qLen⟩ qb)
    (hgl : gb.length = L.pLen) (hyl : yb.length = L.pLen)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (seqs (Checks.publicPrefix M.mm)) s0 fun s6 =>
      Ready L s6 ∧ (∃ v : Bool, word s6.mem L.base Field.mask.offset = mask v) ∧
      OperandBytes s6 L.base usedBytes ⟨.input .q, .qLen⟩ qb ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s6.mem ∧ Keep coreRegs s0 s6 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  have fitq (n : Nat) (h : n < L.subgroup) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.qLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hqf)
  have fitp (n : Nat) (h : n < L.modulus) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.pLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hpf)
  have ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega
  have hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega
  have hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega
  unfold Checks.publicPrefix
  refine WP.seq (WP.mono (readyRange_ok h0 .p Core.generator (by trivial) hg.active
    (by rw [hgl]; omega) (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true hm) fun s1 h1 => ?_)
  have hy1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy
  have hq1 := h1.preserve h0 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb
  refine WP.seq (WP.mono (readyRange_ok h1.ready .p Core.publicValue (by trivial) hy1.active
    (by rw [hyl]; omega) (by simp only [hyl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true h1.mask) fun s2 h2 => ?_)
  have hq2 := h2.preserve h1.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq1
  refine WP.seq (WP.mono (readyMinus_ok h2.ready .p 1 (by decide) (by change 1 ≤ L.modulus; omega)
    t (by decide) ht) fun s3 h3 => ?_)
  have hq3 := h3.external (by decide) ht hq2
  have hm3 := (h3.fields (by decide) ht .mask).trans h2.mask
  have step4 := readyReduce_ok M h3.ready hq hoq (Core.element t) (by change t < 2 ^ 31; decide)
    (h3.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega) u (by decide) hu
  have step4' : WP isa (Core.reduce M.mm (Core.element t) (Core.scalar u)) s3
      (CallResult L .q u ((L.modulus - 1) % L.subgroup) s3) := by
    simpa only [ModulusSide.length, ModulusSide.value, fitp (L.modulus - 1) (by omega)] using step4
  refine WP.seq (WP.mono step4' fun s4 h4 => ?_)
  have hq4 := h4.external (by decide) hu hq3
  have hm4 := (h4.fields (by decide) hu .mask).trans hm3
  refine WP.seq (WP.mono (readyZero_ok h4.ready (Core.scalar u) (by change u < 2 ^ 31; decide)
    (h4.output (by decide) hu) (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) false hm4) fun s5 h5 => ?_)
  have hziff : (∀ b ∈ Spec.Dsa.encodeBE L.qLen ((L.modulus - 1) % L.subgroup), b = 0) ↔
      (L.modulus - 1) % L.subgroup = 0 := by
    rw [← VG.Proof.Dsa.decodeBE_eq_zero, fitq _ (Nat.mod_lt _ (by omega))]
  have hm5 := h5.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length] at hm5
  simp only [hziff] at hm5
  have hq5 := h5.preserve h4.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq4
  refine WP.mono (readyMinus_ok h5.ready .q 2 (by decide) (by change 2 ≤ L.subgroup; omega)
    qMinusTwo (by decide) hqm) fun s6 h6 => ?_
  have hq6 := h6.external (by decide) hqm hq5
  have hm6 := (h6.fields (by decide) hqm .mask).trans hm5
  exact ⟨h6.ready, ⟨_, hm6⟩, hq6,
    (((((h1.scheduleFrame.trans h2.scheduleFrame).trans (h3.scheduleFrame (by decide) ht)).trans
      (h4.scheduleFrame (by decide) hu)).trans h5.scheduleFrame).trans (h6.scheduleFrame (by decide) hqm)),
    (((((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep).trans h5.keep).trans h6.keep).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Constant time of DSA domain and public-key validation -/

/-! # Preserving the public subgroup order through DSA validation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
  have pp (p : SchedulePublic) : 1 ≤ p.layout.pLen := by have := p.layout.widths; omega_using [this]
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
    (by change t < 2 ^ 31; decide) (by simp [stablePointer, Core.element])
    (by intro p; have := p.layout.widths; omega_using [this])
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide)
  have h5 := scheduleZero_ct inputs stable (Core.scalar u) (fun p => p.layout.qLen) false
    (by change u < 2 ^ 31; decide) (by simp [stablePointer, Core.scalar]) (by decide)
    qp (by intro p; have := p.layout.widths; omega_using [this]) (by taint_decide)
  have h6 := scheduleMinus_ct inputs stable .q 2 qMinusTwo (by decide)
    (by intro p; have := p.qGreater; change 2 ≤ p.layout.subgroup; omega_using [this])
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
theorem publicSubgroup_ct (M : Mont) (Sq : MontS) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (a : Operand) (ha : pointerFits a.pointer) (hpa : stablePointer a.pointer)
    (hin : ∀ p, (a, p.layout.pLen) ∈ inputs p)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block (callHead a ⟨.input .q, .qLen⟩ (Core.element t) pWorkspace)) hc).isSome = true) :
    RelCT isa (Two (PublicKeyPre inputs))
      (Core.publicPow Sq.mm M.mm pWorkspace a ⟨.input .q, .qLen⟩ (Core.element t))
      (Two (PublicKeyPre inputs)) := by
  let pub (p : SchedulePublic) : ReadyCallPublic .p t :=
    scheduleCallPublic .p t (fun p => p.layout.pLen) (fun p => p.layout.qLen)
      (by intro p; have := p.layout.widths; omega_using [this]) (fun _ => Nat.le_refl _)
      (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega_using [this])
      (by decide) (element_space (by decide)) p
  refine two_post (two_map (fun p => (pub p, Spec.Dsa.encodeBE p.layout.qLen p.layout.subgroup)) ?_
    (PublicPower.readyPublicPow_ct M Sq .p t a ⟨.input .q, .qLen⟩ ha (by trivial) hpa (by change Field.q ≠ .mask; decide) (by decide) hT)) ?_
  · intro p s ⟨hs, qb, hqb, hql, hqv⟩
    obtain ⟨ab, hab, hal⟩ := hs.2.1 _ (hin p)
    have he : Spec.Dsa.encodeBE p.layout.qLen p.layout.subgroup = qb := by
      rw [← hql, ← hqv, VG.Proof.Dsa.encodeBE_decodeBE]
    rw [he]
    exact ⟨⟨hs.1, ab, qb, hab.active, hqb.active, hal, hql⟩, hqb.active, hql⟩
  · intro p s ⟨hs, qb, hqb, hql, hqv⟩
    obtain ⟨ab, hab, hal⟩ := hs.2.1 _ (hin p)
    refine WP.mono (readyPublicPow_ok M Sq hs.1 .p p.pGreater p.pOdd a ⟨.input .q, .qLen⟩ ha (by trivial)
      hab.active hqb.active (by rw [hal]; have := p.layout.widths; omega)
      (by rw [hal]; exact Nat.le_refl _) (by rw [hql]; exact p.layout.widths.1)
      (by rw [hql]; have := p.layout.widths; omega_using [this]) t (by decide) (element_space (by decide) p))
      fun s' h => ⟨h.schedule hs (by decide) (element_space (by decide) p) (stable p),
        qb, h.external (by decide) (element_space (by decide) p) hqb, hql, hqv⟩

theorem publicIsOne_ct (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer) :
    RelCT isa (Two (PublicKeyPre inputs)) (Checks.isOne pWorkspace (Core.element t))
      (Two (PublicKeyPre inputs)) := by
  have ct := scheduleIsOne_ct inputs stable .p (Core.element t) (fun p => p.layout.pLen)
    (by change t < 2 ^ 31; decide) (by trivial) (by intro p; have := p.layout.widths; omega_using [this])
    (fun _ => Nat.le_refl _) (by taint_decide)
  refine two_post (two_map (fun p => p) (fun p s h =>
    ⟨h.1, h.1.1.availableLocal .p t (by decide) (element_space (by decide) p)⟩) (ct.mono (fun _ _ h => h) (fun _ _ _ => trivial))) ?_
  intro p s ⟨hs, qb, hqb, hql, hqv⟩
  obtain ⟨valid, hm⟩ := hs.2.2
  have hb := hs.1.readLocal .p t (by decide) (element_space (by decide) p)
  have hl : (Spec.Rsa.bytesAt s.mem (off p.layout.base t) p.layout.pLen).length = p.layout.pLen := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  refine WP.mono (readyIsOne_ok hs.1 .p (Core.element t) (by change t < 2 ^ 31; decide) hb
    (by simp only [ModulusSide.length]; rw [hl]; have := p.layout.widths; omega_using [this]) (by simp only [ModulusSide.length]; rw [hl]; exact Nat.le_refl _) hm)
    fun s' h => ⟨h.schedule hs (stable p), qb,
      h.preserve hs.1 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb, hql, hqv⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Constant time of DSA domain and public-key validation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem publicKey_ct (M : Mont) (Sq : MontS) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p)
    (_hq : ∀ p, (⟨.input .q, .qLen⟩, p.layout.qLen) ∈ inputs p) :
    RelCT isa (Two (PublicKeyPre inputs)) (Checks.publicKey Sq.mm M.mm)
      (Two (ScheduleState inputs)) := by
  have hgct := publicSubgroup_ct M Sq inputs stable Core.generator (by trivial) (by simp [stablePointer, Core.generator]) hg (by taint_decide)
  have hyct := publicSubgroup_ct M Sq inputs stable Core.publicValue (by trivial) (by simp [stablePointer, Core.publicValue]) hy (by taint_decide)
  have hone := publicIsOne_ct inputs stable
  unfold Checks.publicKey
  apply RelCT.seqs_append (a := [Checks.range pWorkspace Core.generator true,
    Checks.range pWorkspace Core.publicValue true, Checks.modulusMinus pWorkspace 1 (Core.element t),
    Core.reduce M.mm (Core.element t) (Core.scalar u), Checks.zero (Core.scalar u),
    Checks.modulusMinus qWorkspace 2 (Core.scalar qMinusTwo)]) (by simp) (by simp)
  exact (RelCT.seq (publicPrefix_known_ct M inputs stable hg hy)
    (RelCT.seq hgct (RelCT.seq hone (RelCT.seq hyct hone)))).mono
    (fun _ _ h => h) (fun _ _ ⟨p, hs, ht⟩ => ⟨p, hs.1, ht.1⟩)

theorem signingKey_ct (M : Mont) (Sq : MontS) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p)
    (_hq : ∀ p, (⟨.input .q, .qLen⟩, p.layout.qLen) ∈ inputs p) :
    RelCT isa (Two (PublicKeyPre inputs)) (Checks.signingKey Sq.mm M.mm)
      (Two (ScheduleState inputs)) := by
  have hgct := publicSubgroup_ct M Sq inputs stable Core.generator (by trivial) (by simp [stablePointer, Core.generator]) hg (by taint_decide)
  have hone := publicIsOne_ct inputs stable
  unfold Checks.signingKey
  apply RelCT.seqs_append (a := [Checks.range pWorkspace Core.generator true,
    Checks.range pWorkspace Core.publicValue true, Checks.modulusMinus pWorkspace 1 (Core.element t),
    Core.reduce M.mm (Core.element t) (Core.scalar u), Checks.zero (Core.scalar u),
    Checks.modulusMinus qWorkspace 2 (Core.scalar qMinusTwo)]) (by simp) (by simp)
  exact (RelCT.seq (publicPrefix_known_ct M inputs stable hg hy)
    (RelCT.seq hgct hone)).mono
    (fun _ _ h => h) (fun _ _ ⟨p, hs, ht⟩ => ⟨p, hs.1, ht.1⟩)

end VG.Proof.Dsa.X86_64
