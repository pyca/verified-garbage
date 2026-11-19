module

public import VerifiedGarbage.Proof.Dsa.AArch64.ParametersCT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.Spec.Dsa.DomainChecked
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.AArch64.DeriveChecked
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
public import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveChecked
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
public import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
import VerifiedGarbage.Proof.Dsa.AArch64.CheckOperands
import VerifiedGarbage.Proof.Dsa.AArch64.SharedCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.CheckOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedCall
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeCTState
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.AArch64.ShapeCTState
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Dsa.AArch64.DeriveCheckedCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.DeriveMainCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.DeriveCT`, which this module and modules that import it used -/

section

/-! # Constant time of AArch64 DSA key derivation

x is secret: two calls with the same pointers, lengths and domain take the
same path. Its range check, g^x and the signer's checks run on the signer's
schedule, whose operands' bytes may differ; the copies move secret bytes at
public addresses. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-! ## The entry and the domain's shape -/

theorem deriveEntry_ct : RelCT isa (Two (fun B : Addr => fun s => s.gpr .x7 = B))
    (.block Generate.deriveEntry) (fun _ _ => True) :=
  two_taint [.x7] (pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)) (by taint_decide)

structure DeriveCall where
  input : DeriveInput
  original : State
  pre : DerivePre input original

abbrev DeriveCall.layout (c : DeriveCall) : ExecutionLayout := c.input.layout c.original c.pre.pLength

structure DeriveAgrees (reference c : DeriveCall) : Prop where
  layout : c.layout = reference.layout
  params : c.input.params = reference.input.params
  stack : c.original.sp = reference.original.sp

def DeriveStart (reference : DeriveCall) (s : State) : Prop :=
  ∃ c : DeriveCall, DeriveAgrees reference c ∧ c.original = s

def DeriveEntered (reference : DeriveCall) (s : State) : Prop :=
  ∃ c : DeriveCall, DeriveAgrees reference c ∧
    KeygenEntryPost c.original c.input.base (deriveFieldValues c.original (BitVec.ofNat 64 c.input.qLen)
      c.input.base true) s

def DeriveShaped (reference : DeriveCall) (s : State) : Prop :=
  ∃ c : DeriveCall, DeriveAgrees reference c ∧ DeriveShapePost c.input c.original c.pre.pLength s

theorem DeriveAgrees.pLen {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.input.pLen = reference.input.pLen := congrArg ExecutionLayout.pLen h.layout

theorem DeriveAgrees.qLen {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.input.qLen = reference.input.qLen := congrArg ExecutionLayout.qLen h.layout

theorem DeriveAgrees.pb {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.input.pb = reference.input.pb := by
  rw [ParametersInput.pb, ParametersInput.pb, h.params, h.pLen]

theorem DeriveAgrees.qb {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.input.qb = reference.input.qb := by
  rw [ParametersInput.qb, ParametersInput.qb, h.params, h.pLen, h.qLen]

theorem DeriveAgrees.accepted {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.input.accepted = reference.input.accepted := by
  unfold ParametersInput.accepted
  congr 1
  · exact h.pb
  · exact h.qb

theorem DeriveAgrees.base {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.input.base = reference.input.base := congrArg ExecutionLayout.base h.layout

theorem deriveEntered_ct : RelCT isa (Two DeriveStart) (.block Generate.deriveEntry) (Two DeriveEntered) := by
  refine two_post (two_map (fun c : DeriveCall => c.layout.base) ?_ deriveEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact c.pre.base.trans ha.base
  · intro reference s ⟨c, ha, hs⟩
    subst s
    refine WP.mono (deriveEntry_ok (scratch_prefix c.pre.scratch (by decide) (by decide)) c.pre.base) fun t ht => ?_
    rw [c.pre.qLength] at ht
    exact ⟨c, ha, ht⟩

def DeriveCall.shape (c : DeriveCall) : ShapePublic where
  base := c.layout.base
  extent := usedBytes
  pPointer := c.layout.fields .p
  qPointer := c.layout.fields .q
  pBytes := c.input.pb
  qBytes := c.input.qb
  digestLen := 0
  extentBound := by decide
  pPositive := c.input.pPositive
  qPositive := c.input.qPositive
  pBound := by rw [c.input.pbLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega_using [this]
  qBound := by rw [c.input.qbLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega_using [this]
  digestBound := by decide

theorem DeriveAgrees.shape {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.shape = reference.shape := by
  unfold DeriveCall.shape
  congr 1
  · exact congrArg ExecutionLayout.base h.layout
  · exact congrArg (fun L => L.fields .p) h.layout
  · exact congrArg (fun L => L.fields .q) h.layout
  · exact h.pb
  · exact h.qb

theorem DeriveEntered.context {reference : DeriveCall} {s : State} (h : DeriveEntered reference s) :
    ShapeContext reference.shape s := by
  obtain ⟨c, ha, he⟩ := h
  rw [← ha.shape]
  have hf : InScr c.input.base deriveExtent c.original.mem s.mem := InScr.of_outside he.frame (by decide)
  obtain ⟨hps, hqs, _, _⟩ := c.pre.sources hf (he.keep.mono (by decide))
  have hu : usedBytes ≤ deriveExtent := by decide
  refine ⟨scratch_prefix (n := usedBytes) (c.pre.scratch.congr he.keep.wr) hu (by decide), he.base,
    he.fields .p (by decide) (by decide), he.fields .q (by decide) (by decide), ?_, ?_,
    he.fields .digestLen (by decide) (by decide), source_shrink hps hu, source_shrink hqs hu⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.pb.length
    rw [c.input.pbLength]
    exact (he.fields .pLen (by decide) (by decide)).trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.qb.length
    rw [c.input.qbLength]
    exact he.fields .qLen (by decide) (by decide)

theorem deriveShape_ct : RelCT isa (Two DeriveStart)
    (.seq (.block Generate.deriveEntry) Checks.domainShape) (Two DeriveShaped) := by
  refine two_post (RelCT.seq deriveEntered_ct
    (two_map DeriveCall.shape (fun _ _ h => h.context) domainShape_ct)) ?_
  intro reference s ⟨c, ha, hs⟩
  subst s
  exact WP.mono (deriveShape_ok c.pre) fun t ht => ⟨c, ha, ht⟩

theorem DeriveShaped.branch {reference : DeriveCall} {s : State} (h : DeriveShaped reference s) :
    eval (.zero .x .x3) s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change some (s.gpr .x3 == (0#64)) = _
  rw [hs.branch, ha.accepted]

/-! ## A malformed domain -/

structure DeriveFailurePublic where
  base : Addr
  output : Addr
  width : Nat

def DeriveFailurePre (p : DeriveFailurePublic) (s : State) : Prop :=
  s.gpr .x0 = p.base ∧ ∃ pLen qLen : Nat, p.width = 3 * pLen + 2 * qLen ∧
    Scr s p.base pWorkspace ∧ word s.mem p.base Field.out.offset = p.output ∧
    word s.mem p.base Field.pLen.offset = BitVec.ofNat 64 pLen ∧
    word s.mem p.base Field.qLen.offset = BitVec.ofNat 64 qLen

def DeriveFailureRegs (p : DeriveFailurePublic) (s : State) : Prop :=
  s.gpr .x0 = p.base ∧ s.gpr .x1 = p.output ∧ s.gpr .x2 = BitVec.ofNat 64 p.width

theorem deriveFailure_ct : RelCT isa (Two DeriveFailurePre) Generate.deriveFailure (fun _ _ => True) := by
  unfold Generate.deriveFailure seqs
  refine RelCT.seq (two_piece (Ψ := DeriveFailureRegs) [.x0]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact h.1)) (by taint_decide) ?_) ?_
  · intro p s ⟨hdi, pl, ql, hw, hs, ho, hp, hq⟩
    refine WP.mono (WP.keep [.x3, .x1, .x2] (Q := fun t =>
      t.gpr .x1 = p.output ∧ t.gpr .x2 = BitVec.ofNat 64 p.width) ?_ rfl rfl rfl)
      fun t ⟨⟨hsi, hcx⟩, hk⟩ => ⟨(hk.gpr .x0 (by decide)).trans hdi, hsi, hcx⟩
    brun [Core.field, field_enc .out, field_enc .pLen, field_enc .qLen, fieldAddress, hdi, ho, hp, hq,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 (Nat.le_refl _)),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .pLen).2 (Nat.le_refl _)),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 (Nat.le_refl _))]
    simp only [BitVec.ofNat_add_ofNat, hw]
    congr 1
    omega_using []
  · exact two_taint [.x0, .x1, .x2]
      (pins_of (fun p r => if r = .x0 then p.base else if r = .x1 then p.output else BitVec.ofNat 64 p.width)
        (by
          intro p s h r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2)) (by taint_decide)

def DeriveCall.failure (c : DeriveCall) : DeriveFailurePublic where
  base := c.layout.base
  output := c.layout.fields .out
  width := c.input.outLen

theorem DeriveShaped.failure {reference : DeriveCall} {s : State} (h : DeriveShaped reference s) :
    DeriveFailurePre reference.failure s := by
  obtain ⟨c, ha, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .x0 = c.layout.base := hs.x0
  have hscr : Scr s c.layout.base pWorkspace := scratch_prefix hs.scratch (by decide) (by decide)
  have hw : reference.input.outLen = 3 * reference.layout.pLen + 2 * reference.layout.qLen := rfl
  rw [ha.layout] at hf hr hscr
  exact ⟨hr, reference.layout.pLen, reference.layout.qLen, hw, hscr, hf .out,
    (hf .pLen).trans reference.layout.pLength, (hf .qLen).trans reference.layout.qLength⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.DeriveBodyCT`, which this module and modules that import it used -/

section

/-! # Constant time of derivation's computation: x's range, g^x with g^q, y's copy and the key checks

The operands' bytes may differ between two calls, x's among them: the
schedule relates two runs by their public layout alone. The subgroup order's
bytes are kept exactly, at derivation's extent, for the key checks. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

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
    rw [hk.rd, hk.wr, hptr]
    exact hb.source.rd i (by omega_using [hl, hi])
  · intro i hi
    simp [Spec.Rsa.bytesAt]
  · intro i hi
    rw [bytesAt_length] at hi
    rw [hptr]
    exact hb.source.out i (by omega_using [hl, hi])
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
  exact ⟨h.schedule hs (fun a ha => deriveInputs_stable p a ha), hscr.congr h.keep.wr,
    qb, h.preserve hs.1 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb, hql, hqv⟩

theorem derivePow_ct (M : Mont) : RelCT isa (Two DeriveSched)
    (Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2)) (Two DeriveSched) := by
  have hend (p : SchedulePublic) : t2 + ModulusSide.p.length p.layout ≤ usedBytes := element_space (by decide) p
  have ct := schedulePow_ct M deriveInputs (fun p => deriveInputs_stable p) .p t2 Core.generator
    Core.privateScalar (fun p => p.layout.pLen) (fun p => p.layout.qLen) (by trivial) (by trivial)
    (by simp [stablePointer, Core.generator]) (by simp [stablePointer, Core.privateScalar])
    (by intro p; have := p.layout.widths; omega_using [this]) (fun _ => Nat.le_refl _)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega_using [this])
    (by decide) (by decide) hend (by taint_decide)
  refine two_post ((two_map (fun p => p) (fun p s h => ⟨h.1,
    (h.1.2.1 (Core.generator, p.layout.pLen) (by simp [deriveInputs])).active,
    (h.1.2.1 (Core.privateScalar, p.layout.qLen) (by simp [deriveInputs])).active⟩) ct).mono (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro p s ⟨hs, hscr, qb, hqb, hql, hqv⟩
  obtain ⟨ga, hga, hgl⟩ := hs.2.1 _ (show (Core.generator, p.layout.pLen) ∈ deriveInputs p by
    simp [deriveInputs])
  obtain ⟨xa, hxa, hxl⟩ := hs.2.1 _ (show (Core.privateScalar, p.layout.qLen) ∈ deriveInputs p by
    simp [deriveInputs])
  have step := readyPow_ok M hs.1 .p (p.greater .p) (p.odd .p) Core.generator Core.privateScalar
    (by trivial) (by trivial) hga.active hxa.active (by rw [hgl]; have := p.layout.widths; omega)
    (by rw [hgl]; exact Nat.le_refl _) (by rw [hxl]; exact p.layout.widths.1)
    (by rw [hxl]; have := p.layout.widths; omega) t2 (by decide) (hend p)
  refine WP.mono (by simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField] using step)
    fun t h => ?_
  have hf : Outside p.layout.base 128 (deriveExtent - 128) s.mem t.mem :=
    (h.scheduleFrame (by decide) (hend p)).mono (by decide) (by decide)
  exact ⟨h.schedule hs (by decide) (hend p) (fun a ha => deriveInputs_stable p a ha), hscr.congr h.keep.wr,
    qb, hqb.frame hs.1 h.ready hf h.keep (by decide) (by change Field.q ≠ .mask; decide), hql, hqv⟩

def CopyRegs (p : SchedulePublic) (s : State) : Prop :=
  s.gpr .x1 = off p.layout.base t2 ∧ s.gpr .x2 = off p.layout.base derivedY ∧
    s.gpr .x9 = BitVec.ofNat 64 p.layout.pLen

theorem deriveCopy_ct : RelCT isa (Two DeriveSched) Generate.copyY (Two DeriveSched) := by
  have ct : RelCT isa (Two DeriveSched) Generate.copyY (fun _ _ => True) := by
    unfold Generate.copyY seqs
    refine RelCT.seq (two_piece (Ψ := CopyRegs) [.x0]
      (pins_of (fun p _ => p.layout.base) (by
        intro p s h r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact h.1.1.parent.x0)) (by taint_decide) ?_) ?_
    · intro p s h
      exact WP.mono (copyHead_ok h.1.1) fun t ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3⟩
    · exact two_taint [.x1, .x2, .x9]
        (pins_of (fun p r => if r = .x1 then off p.layout.base t2 else if r = .x2 then off p.layout.base derivedY
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
    hscr.congr hk.wr, qb, hqb.frame hs.1 ht hf' hk (by decide) (by change Field.q ≠ .mask; decide), hql, hqv⟩

/-- y = g^x and whether `g^q = 1`, in one pass: q's bytes are the public
subgroup order's. -/
theorem deriveSharedPow_ct (M : Mont) : RelCT isa (Two DeriveSched)
    (SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t2)) (Two DeriveSched) := by
  have hend (p : SchedulePublic) : t2 + ModulusSide.p.length p.layout ≤ usedBytes := element_space (by decide) p
  have qsrc {p : SchedulePublic} {s : State} (h : DeriveSched p s) :
      Src s p.layout.base activeBytes (p.layout.fields .q)
        (Spec.Dsa.encodeBE p.layout.qLen p.layout.subgroup) := by
    obtain ⟨hs, _, qb, hqb, hql, hqv⟩ := h
    rw [← hs.1.fields .q (by decide), ← hql, ← hqv, VG.Proof.Dsa.encodeBE_decodeBE]
    exact ((hqb.shrink (by decide)).active).source
  refine two_post (two_map (fun p : SchedulePublic => (⟨⟨p.layout, p.layout.pLen, p.layout.qLen, p.greater .p,
      p.odd .p, by have := p.layout.widths; omega_using [this], Nat.le_refl _, p.layout.widths.1,
      by have := p.layout.widths; omega_using [this], by decide, hend p⟩,
      Spec.Dsa.encodeBE p.layout.qLen p.layout.subgroup, VG.Proof.Dsa.encodeBE_length _ _⟩ :
        SharedPower.ReadySharedPublic t2)) (fun p s h => ?_)
    (SharedPower.readySharedPow_ct M t2 Core.generator Core.privateScalar (by trivial) (by trivial)
      (by simp [stablePointer, Core.generator]) (by simp [stablePointer, Core.privateScalar]) (by decide)
      (by taint_decide))) ?_
  · obtain ⟨ga, hga, hgl⟩ := h.1.2.1 _ (show (Core.generator, p.layout.pLen) ∈ deriveInputs p by
      simp [deriveInputs])
    obtain ⟨xa, hxa, hxl⟩ := h.1.2.1 _ (show (Core.privateScalar, p.layout.qLen) ∈ deriveInputs p by
      simp [deriveInputs])
    exact ⟨⟨h.1.1, ga, xa, hga.active, hxa.active, hgl, hxl⟩, qsrc h⟩
  intro p s h
  have hq := qsrc h
  obtain ⟨hs, hscr, qb, hqb, hql, hqv⟩ := h
  obtain ⟨ga, hga, hgl⟩ := hs.2.1 _ (show (Core.generator, p.layout.pLen) ∈ deriveInputs p by
    simp [deriveInputs])
  obtain ⟨xa, hxa, hxl⟩ := hs.2.1 _ (show (Core.privateScalar, p.layout.qLen) ∈ deriveInputs p by
    simp [deriveInputs])
  obtain ⟨valid, hm⟩ := hs.2.2
  have hq' : Src s p.layout.base activeBytes (word s.mem p.layout.base Field.q.offset)
      (Spec.Dsa.encodeBE p.layout.qLen p.layout.subgroup) := by
    rw [hs.1.fields .q (by decide)]; exact hq
  refine WP.mono (SharedPower.readySharedPow_ok M hs.1 (p.greater .p) (p.odd .p) Core.generator
    Core.privateScalar (by trivial) (by trivial) hga.active hxa.active
    hq' ((VG.Proof.Dsa.encodeBE_length _ _).trans hxl.symm)
    (by rw [hgl]; have := p.layout.widths; omega_using [this]) (by rw [hgl])
    (by rw [hxl]; exact p.layout.widths.1) (by rw [hxl]; have := p.layout.widths; omega_using [this])
    t2 (by decide) (hend p) hm) fun t ⟨u, h2, h2c⟩ => ?_
  have hfu : Outside p.layout.base 128 (deriveExtent - 128) s.mem u.mem :=
    (h2.scheduleFrame (by decide) (hend p)).mono (by decide) (by decide)
  have hf2 : Outside p.layout.base 128 (deriveExtent - 128) u.mem t.mem :=
    h2c.frame.mono (by decide) (by decide)
  have stable := fun a ha => deriveInputs_stable p a ha
  exact ⟨h2c.schedule (h2.schedule hs (by decide) (hend p) stable) stable,
    hscr.congr (h2.keep.trans h2c.keep).wr, qb,
    (hqb.frame hs.1 h2.ready hfu h2.keep (by decide) (by change Field.q ≠ .mask; decide)).frame h2.ready
      h2c.ready hf2 h2c.keep (by decide) (by change Field.q ≠ .mask; decide), hql, hqv⟩

theorem deriveBodySched_ct (M : Mont) : RelCT isa (Two DeriveSched)
    (seqs [Checks.range qWorkspace Core.privateScalar,
      SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, seqs (Checks.publicPrefix M.mm)]) (fun _ _ => True) := by
  have h4 := publicPrefix_ct M deriveInputs (fun p => deriveInputs_stable p)
    (by intro p; simp [deriveInputs]) (by intro p; simp [deriveInputs])
  unfold seqs
  refine RelCT.seq deriveRange_ct (RelCT.seq (deriveSharedPow_ct M) (RelCT.seq deriveCopy_ct ?_))
  exact (two_map (Φ := DeriveSched) (fun p => p) (fun p s h => h.1) h4).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of the complete AArch64 key derivation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-! ## Writing the key at public addresses -/

structure KeyPublic where
  base : Addr
  out : Addr
  params : Addr
  publicValue : Addr
  scalar : Addr
  pLen : Nat
  qLen : Nat

def KeyPre (k : KeyPublic) (s : State) : Prop :=
  s.gpr .x0 = k.base ∧ Scr s k.base pWorkspace ∧
  (∃ valid, KeyFields s k.base k.out k.params k.publicValue k.scalar k.pLen k.qLen valid) ∧
  0 < k.pLen ∧ 0 < k.qLen ∧ 3 * k.pLen + 2 * k.qLen < 2 ^ 64 ∧
  KeySource s k.params k.out (2 * k.pLen + k.qLen) (3 * k.pLen + 2 * k.qLen) ∧
  KeySource s k.publicValue k.out k.pLen (3 * k.pLen + 2 * k.qLen) ∧
  KeySource s k.scalar k.out k.qLen (3 * k.pLen + 2 * k.qLen) ∧
  (∀ i < 3 * k.pLen + 2 * k.qLen, InRegions s.wr (k.out + BitVec.ofNat 64 i) 1)

def KeyHeadRegs (k : KeyPublic) (s : State) : Prop :=
  s.gpr .x0 = k.base ∧ s.gpr .x1 = k.params ∧ s.gpr .x2 = k.out ∧
  s.gpr .x9 = BitVec.ofNat 64 (2 * k.pLen + k.qLen) ∧
  KeyRegs s k.out k.publicValue k.scalar k.pLen k.qLen

theorem writeKey_ct : RelCT isa (Two KeyPre) Generate.writeKey
    (Two (fun (k : KeyPublic) (s : State) => s.gpr .x0 = k.base)) := by
  have ct : RelCT isa (Two KeyPre) Generate.writeKey (fun _ _ => True) := by
    unfold Generate.writeKey seqs
    refine RelCT.seq (two_piece (Ψ := KeyHeadRegs) [.x0]
      (pins_of (fun (k : KeyPublic) _ => k.base) (by
        intro k s h r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact h.1)) (by taint_decide) ?_) ?_
    · intro k s ⟨hdi, hs, ⟨valid, hf⟩, _⟩
      exact WP.mono (keyHead_ok hs hdi (Nat.le_refl _) hf) fun t ⟨h1, h2, h3, _, _, hk, hr⟩ =>
        ⟨(hk.gpr .x0 (by decide)).trans hdi, h1, h2, h3, hr⟩
    · exact two_taint [.x0, .x1, .x2, .x9, .x11, .x12, .x13, .x14, .x10]
        (pins_of (fun k r => match r with
            | .x0 => k.base | .x1 => k.params | .x2 => k.out
            | .x9 => BitVec.ofNat 64 (2 * k.pLen + k.qLen) | .x11 => k.publicValue | .x12 => k.scalar
            | .x13 => BitVec.ofNat 64 k.pLen | .x14 => BitVec.ofNat 64 k.qLen | _ => k.out)
          (by
            intro k s h r hr
            obtain ⟨h1, h2, h3, h4, h5⟩ := h
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact h1
            · exact h2
            · exact h3
            · exact h4
            · exact h5.publicValue
            · exact h5.scalar
            · exact h5.pLen
            · exact h5.qLen
            · exact h5.out)) (by taint_decide)
  refine two_post ct ?_
  intro k s ⟨hdi, hs, ⟨valid, hf⟩, hp, hq, hk, hP, hY, hX, hw⟩
  exact WP.mono (writeKey_ok hs hdi (Nat.le_refl _) hf hp hq hk hP hY hX hw)
    fun t ⟨_, _, _, _, hkt⟩ => (hkt.gpr .x0 (by decide)).trans hdi

/-! ## Two calls through the computation -/

def DeriveCall.schedule (c : DeriveCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
  layout := c.layout.withInverses pi qi
  digestLen := 0
  pGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).1
  qGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).2.1
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2
  pFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.pb
    rw [c.input.pbLength] at h
    exact Nat.le_of_lt h
  qFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.qb
    rw [c.input.qbLength] at h
    exact Nat.le_of_lt h
  digestBound := by decide

def DeriveCall.initialization (c : DeriveCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.pb
  qBytes := c.input.qb
  pLength := c.input.pbLength
  qLength := c.input.qbLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem DeriveShaped.initialization {reference : DeriveCall} {s : State}
    (h : DeriveShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .x0 = c.layout.base := hs.x0
  have hscr : Scr s c.layout.base usedBytes := scratch_prefix (n := usedBytes) hs.scratch (by decide) (by decide)
  obtain ⟨hps, hqs, _, _⟩ := c.pre.sources hs.frame hs.keep
  have hps' : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.pb := source_shrink hps (by decide)
  have hqs' : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.qb := source_shrink hqs (by decide)
  rw [hag.layout] at hf hr hscr hps' hqs'
  rw [hag.pb] at hps'
  rw [hag.qb] at hqs'
  exact ⟨hscr, hr, hf, hps', hqs'⟩

abbrev AcceptedDeriveCall := {c : DeriveCall // c.input.accepted = true}

def DeriveReady (reference : DeriveCall) (s : State) : Prop :=
  ∃ c : DeriveCall, DeriveAgrees reference c ∧ DeriveInitialized c.input c.original c.pre.pLength s

theorem deriveWorkspaces_ct : RelCT isa (Two (fun c : AcceptedDeriveCall => DeriveShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedDeriveCall => DeriveReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedDeriveCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (deriveInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

theorem DeriveReady.sched {reference : DeriveCall} {s : State} (ha : reference.input.accepted = true)
    (h : DeriveReady reference s) : ∃ pi qi, DeriveSched (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, hframe, hk⟩ := h
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  have hscr : Scr s c.layout.base deriveExtent := c.pre.scratch.congr hk.wr
  change Ready (c.layout.withInverses pi qi) s at hr
  change DeriveOperands (c.layout.withInverses pi qi) c.input s at ho
  have hy : Ready (c.layout.withInverses pi qi) s := hr
  rw [hag.layout] at hr ho hmask hscr
  have hgl : c.input.gb.length = reference.layout.pLen := c.input.gbLength.trans hag.pLen
  have hql : c.input.qb.length = reference.layout.qLen := c.input.qbLength.trans hag.qLen
  have hxl : c.input.x.length = reference.layout.qLen := c.input.xLength.trans hag.qLen
  have hp384 : reference.layout.pLen ≤ 384 := reference.layout.widths.2.2.2
  refine ⟨pi, qi, ⟨hr, ?_, ⟨true, hmask⟩⟩, hscr, c.input.qb, ho.subgroup, hql, ?_⟩
  · intro a ha
    simp only [deriveInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · -- y's slot, past the signer's layout
      have hyw : word s.mem reference.layout.base Field.y.offset = off reference.layout.base derivedY :=
        hr.fields .y (by decide)
      refine ⟨Spec.Rsa.bytesAt s.mem (off reference.layout.base derivedY) reference.layout.pLen,
        ⟨?_, ?_, ?_, ?_⟩, bytesAt_length _ _ _⟩
      · rw [bytesAt_length]
        exact (hr.fields .pLen (by decide)).trans reference.layout.pLength
      · intro i hi
        rw [bytesAt_length] at hi
        show InRegions (s.rd ++ s.wr) (word s.mem reference.layout.base Field.y.offset + BitVec.ofNat 64 i) 1
        rw [hyw, off_add]
        exact scr_byte_rd hscr (by unfold deriveExtent; omega_using [hp384, hi])
      · intro i hi
        show s.mem (word s.mem reference.layout.base Field.y.offset + BitVec.ofNat 64 i) = _
        rw [hyw]
        simp [Spec.Rsa.bytesAt]
      · intro i hi
        rw [bytesAt_length] at hi
        show usedBytes ≤ ofs reference.layout.base (word s.mem reference.layout.base Field.y.offset + BitVec.ofNat 64 i)
        rw [hyw, ofs_off _ (by have := hscr.nowrap; unfold deriveExtent at this; omega_using [hp384, hi, this])]
        exact Nat.le_add_right _ _
    · exact ⟨_, ho.subgroup.shrink (by decide), hql⟩
    · exact ⟨_, ho.generator.shrink (by decide), hgl⟩
    · exact ⟨_, ho.scalar.shrink (by decide), hxl⟩
  · change Spec.Dsa.decodeBE c.input.qb = Spec.Dsa.decodeBE reference.input.qb
    rw [hag.qb]

theorem deriveReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedDeriveCall => DeriveReady c.val) s₁ s₂) : Two DeriveSched s₁ s₂ := by
  obtain ⟨reference, h₁, h₂, hsp⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.sched reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.sched reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1.1 h₂.1.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂, hsp⟩

/-- After the computation: what writing the key needs. -/
def DeriveComputed (reference : DeriveCall) (s : State) : Prop :=
  ∃ c : DeriveCall, DeriveAgrees reference c ∧ ∃ pi qi valid,
    Ready (c.layout.withInverses pi qi) s ∧ word s.mem c.input.base Field.mask.offset = mask valid ∧
    InScr c.input.base deriveExtent c.original.mem s.mem ∧ Keep coreRegs c.original s

def DeriveCall.key (c : DeriveCall) : KeyPublic where
  base := c.layout.base
  out := c.layout.fields .out
  params := c.layout.fields .p
  publicValue := c.layout.fields .y
  scalar := c.layout.fields .x
  pLen := c.layout.pLen
  qLen := c.layout.qLen

theorem DeriveComputed.key {reference : DeriveCall} {s : State} (h : DeriveComputed reference s) :
    KeyPre reference.key s := by
  obtain ⟨c, hag, pi, qi, valid, hr, hm, hframe, hk⟩ := h
  have hkey : c.key = reference.key := by unfold DeriveCall.key; rw [hag.layout]
  rw [← hkey]
  have hl : Spec.Dsa.lengthsValid c.key.pLen c.key.qLen := c.input.lengths
  unfold Spec.Dsa.lengthsValid at hl
  have hscr : Scr s c.input.base deriveExtent := c.pre.scratch.congr hk.wr
  have hn := hscr.nowrap
  obtain ⟨_, _, _, hxs⟩ := c.pre.sources hframe hk
  have hparams := c.pre.paramsSource.congrK hframe hk
  have hf (f : Field) (hf : f ≠ .mask) : word s.mem c.input.base f.offset = c.layout.fields f := hr.fields f hf
  refine ⟨hr.parent.x0, scratch_prefix (n := pWorkspace) hscr (by decide) (by decide),
    ⟨valid, hf .out (by decide), hf .p (by decide), hf .y (by decide), hf .x (by decide),
      (hf .pLen (by decide)).trans c.pre.pLength, hf .qLen (by decide), hm⟩,
    by omega_using [hl], by omega_using [hl], by omega_using [hl],
    ⟨fun i hi => by rw [hk.rd, hk.wr]; exact c.pre.paramsSource.rd i (by rw [c.input.paramsLength]; exact hi),
      c.pre.paramsOut⟩,
    ⟨fun i hi => by
      change InRegions (s.rd ++ s.wr) (off c.input.base derivedY + BitVec.ofNat 64 i) 1
      rw [off_add]
      exact scr_byte_rd hscr (by unfold deriveExtent derivedY usedBytes; omega_using [hi, hl]),
     fun i hi j hj => scr_ne_out c.pre.outSeparate (d := derivedY) (i := i)
      (by unfold deriveExtent derivedY usedBytes; omega_using [hi, hl]) (by omega_using [hn]) j hj⟩,
    ⟨fun i hi => by rw [hk.rd, hk.wr]; exact c.pre.xSource.rd i (by rw [c.input.xLength]; exact hi),
      c.pre.xOut⟩,
    fun i hi => by rw [hk.wr]; exact c.pre.outWrite i hi⟩

theorem deriveComputed_ok (M : Mont) {reference : AcceptedDeriveCall} {s : State}
    (h : DeriveReady reference.val s) :
    WP isa (seqs [Checks.range qWorkspace Core.privateScalar,
      SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, seqs (Checks.publicPrefix M.mm)]) s (DeriveComputed reference.val) := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, hframe, hk⟩ := h
  have hac : c.input.accepted = true := hag.accepted.trans reference.property
  obtain ⟨hsize, hpo, hqo⟩ := c.input.shapeFacts hac
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have hpf : Spec.Dsa.decodeBE c.input.pb ≤ 256 ^ c.input.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt c.input.pb; rw [c.input.pbLength] at hh; exact Nat.le_of_lt hh
  have hqf : Spec.Dsa.decodeBE c.input.qb ≤ 256 ^ c.input.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt c.input.qb; rw [c.input.qbLength] at hh; exact Nat.le_of_lt hh
  refine WP.mono (deriveBody_ok (L := c.layout.withInverses pi qi) M hr (c.pre.scratch.congr hk.wr)
    hp1 hq255 hpo hqo hpf hqf ho.generator ho.subgroup ho.scalar c.input.gbLength c.input.qbLength
    c.input.xLength rfl hm) fun t ⟨ht, hmt, _, hft, hkt⟩ => ?_
  exact ⟨c, hag, pi, qi, _, ht, hmt, hframe.trans (InScr.of_outside hft (by decide)),
    (hk.trans hkt).mono (by decide)⟩

theorem deriveSuccess_ct (M : Mont) :
    RelCT isa (Two (fun c : AcceptedDeriveCall => DeriveShaped c.val))
      (seqs [SignVerify.workspaces, Checks.range qWorkspace Core.privateScalar,
        SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t2),
        Generate.copyY, seqs (Checks.publicPrefix M.mm), Generate.writeKey, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq deriveWorkspaces_ct ?_
  apply RelCT.seqs_append (a := [Checks.range qWorkspace Core.privateScalar,
    SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t2),
    Generate.copyY, seqs (Checks.publicPrefix M.mm)]) (b := [Generate.writeKey, .block SignVerify.result])
    (by simp) (by simp)
  refine RelCT.seq (R := Two (fun c : AcceptedDeriveCall => DeriveComputed c.val))
    (two_post ((deriveBodySched_ct M).mono (fun _ _ h => deriveReady_related h) (fun _ _ h => h))
      (fun reference s h => deriveComputed_ok M h)) ?_
  unfold seqs
  exact RelCT.seq (two_map (fun c : AcceptedDeriveCall => c.val.key) (fun _ _ h => h.key) writeKey_ct)
    (two_map (fun k : KeyPublic => k.base) (fun _ _ h => h) result_ct)

theorem deriveMain_ct (M : Mont) :
    RelCT isa (Two DeriveStart) (Generate.deriveKey M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq deriveShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂, hsp⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map DeriveCall.failure (fun _ _ h => h.failure) deriveFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (deriveSuccess_ct M).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂, hsp⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval (.zero .x .x3) s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of AArch64 DSA key derivation for a checked domain -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem deriveCheckedBodySched_ct (M : Mont) : RelCT isa (Two DeriveSched)
    (seqs [Checks.range qWorkspace Core.privateScalar,
      Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, seqs (Checks.publicPrefix M.mm)]) (fun _ _ => True) := by
  have h4 := publicPrefix_ct M deriveInputs (fun p => deriveInputs_stable p)
    (by intro p; simp [deriveInputs]) (by intro p; simp [deriveInputs])
  unfold seqs
  refine RelCT.seq deriveRange_ct (RelCT.seq (derivePow_ct M) (RelCT.seq deriveCopy_ct ?_))
  exact (two_map (Φ := DeriveSched) (fun p => p) (fun p s h => h.1) h4).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem deriveCheckedComputed_ok (M : Mont) {reference : AcceptedDeriveCall} {s : State}
    (h : DeriveReady reference.val s) :
    WP isa (seqs [Checks.range qWorkspace Core.privateScalar,
      Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, seqs (Checks.publicPrefix M.mm)]) s (DeriveComputed reference.val) := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, hframe, hk⟩ := h
  have hac : c.input.accepted = true := hag.accepted.trans reference.property
  obtain ⟨hsize, hpo, hqo⟩ := c.input.shapeFacts hac
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have hpf : Spec.Dsa.decodeBE c.input.pb ≤ 256 ^ c.input.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt c.input.pb; rw [c.input.pbLength] at hh; exact Nat.le_of_lt hh
  have hqf : Spec.Dsa.decodeBE c.input.qb ≤ 256 ^ c.input.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt c.input.qb; rw [c.input.qbLength] at hh; exact Nat.le_of_lt hh
  refine WP.mono (deriveCheckedBody_ok (L := c.layout.withInverses pi qi) M hr (c.pre.scratch.congr hk.wr)
    hp1 hq255 hpo hqo hpf hqf ho.generator ho.subgroup ho.scalar c.input.gbLength
    c.input.xLength rfl hm) fun t ⟨ht, hmt, _, hft, hkt⟩ => ?_
  exact ⟨c, hag, pi, qi, _, ht, hmt, hframe.trans (InScr.of_outside hft (by decide)),
    (hk.trans hkt).mono (by decide)⟩

theorem deriveCheckedSuccess_ct (M : Mont) :
    RelCT isa (Two (fun c : AcceptedDeriveCall => DeriveShaped c.val))
      (seqs [SignVerify.workspaces, Checks.range qWorkspace Core.privateScalar,
        Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
        Generate.copyY, seqs (Checks.publicPrefix M.mm), Generate.writeKey, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq deriveWorkspaces_ct ?_
  apply RelCT.seqs_append (a := [Checks.range qWorkspace Core.privateScalar,
    Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
    Generate.copyY, seqs (Checks.publicPrefix M.mm)]) (b := [Generate.writeKey, .block SignVerify.result])
    (by simp) (by simp)
  refine RelCT.seq (R := Two (fun c : AcceptedDeriveCall => DeriveComputed c.val))
    (two_post ((deriveCheckedBodySched_ct M).mono (fun _ _ h => deriveReady_related h) (fun _ _ h => h))
      (fun reference s h => deriveCheckedComputed_ok M h)) ?_
  unfold seqs
  exact RelCT.seq (two_map (fun c : AcceptedDeriveCall => c.val.key) (fun _ _ h => h.key) writeKey_ct)
    (two_map (fun k : KeyPublic => k.base) (fun _ _ h => h) result_ct)

theorem deriveCheckedMain_ct (M : Mont) :
    RelCT isa (Two DeriveStart) (Generate.deriveChecked M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq deriveShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂, hsp⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map DeriveCall.failure (fun _ _ h => h.failure) deriveFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (deriveCheckedSuccess_ct M).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂, hsp⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval (.zero .x .x3) s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.DeriveCheckedVerified`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.PrevalidatedSat`, which this module and modules that import it used -/

section

/-! # An explicit algebraically consistent domain witnesses the validated precondition

The contract checks algebraic consistency rather than primality. Let a=q·2^352,
q=3·(2^158+1), p=a²+a+1 and g=y=a. Then q divides p−1 and g³=1 mod p.
This is a satisfiability witness, not a cryptographic domain or a test vector.
-/

@[expose] public section
namespace VG.Proof.Dsa.AArch64

def validatedSatKey : List Byte :=
  let q := 3 * (2 ^ 158 + 1)
  let a := q * 2 ^ 352
  Spec.Dsa.encodeBE 128 (a * a + a + 1) ++ Spec.Dsa.encodeBE 20 q ++
    Spec.Dsa.encodeBE 128 a ++ Spec.Dsa.encodeBE 128 a

theorem validatedSatKey_valid : Spec.Dsa.validatePublicKeyBytes 128 20 validatedSatKey = true := by
  decide +kernel

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.DeriveVerified`, which this module and modules that import it used -/

section

/-! # AArch64 DSA key derivation verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem deriveStackArgs (s : State) : List.map (stackArg s) (List.range 1) =
    [stackArg s 0] := rfl

theorem disjoint_byte_ne {p q : Addr} {n m i j : Nat} (h : (⟨p, n⟩ : Region).Disjoint ⟨q, m⟩)
    (hi : i < n) (hj : j < m) (hn : n ≤ 2 ^ 64) (hm : m ≤ 2 ^ 64) :
    p + BitVec.ofNat 64 i ≠ q + BitVec.ofNat 64 j := fun he =>
  h _ (contains_byte p hi hn) (he ▸ contains_byte q hj hm)

structure DeriveABI (s : State) : Prop where
  stackBound : s.sp.toNat + 8 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x5, (s.gpr .x6).toNat⟩, ⟨stackArgAddr s 0, 8⟩]
  wr : s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩]
  outParams : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  outScalar : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  outScratch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩
  paramsScratch : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩
  scalarScratch : (⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩
  scratchArgs : (⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 8⟩
  outBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  paramsBound : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  scalarBound : (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64
  scratchBound : (s.gpr .x7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .x4).toNat (s.gpr .x6).toNat
  outLength : (s.gpr .x1).toNat = 3 * (s.gpr .x4).toNat + 2 * (s.gpr .x6).toNat
  paramsLength : (s.gpr .x3).toNat = 2 * (s.gpr .x4).toNat + (s.gpr .x6).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .x4).toNat ≤ (stackArg s 0).toNat

theorem deriveABI_of {s : State} (h : (Spec.Dsa.deriveKeyContract abi).pre s) : DeriveABI s := by
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at h
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at h
  sig_split h
  constructor <;> with_reducible assumption

def DeriveABI.input {s : State} (h : DeriveABI s) : DeriveInput where
  base := s.gpr .x7
  pLen := (s.gpr .x4).toNat
  qLen := (s.gpr .x6).toNat
  params := Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat
  lengths := h.lengths
  paramsLength := (bytesAt_length _ _ _).trans h.paramsLength
  x := Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat
  xLength := bytesAt_length _ _ _

theorem DeriveABI.used {s : State} (h : DeriveABI s) : deriveExtent ≤ (stackArg s 0).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 16096 ≤ _
  omega_using [hl, hs]

theorem DeriveABI.pre {s : State} (h : DeriveABI s) : DerivePre h.input s := by
  have hs : Scr s (s.gpr .x7) ((stackArg s 0).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  have hout : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  have hol : h.input.outLen = (s.gpr .x1).toNat := h.outLength.symm
  have hu : usedBytes ≤ deriveExtent := by decide
  refine ⟨scratch_prefix hs h.used (by decide), (ofNat_toNat64 _).symm, rfl, (ofNat_toNat64 _).symm,
    source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x3).isLt) h.paramsScratch) h.used,
    source_shrink (src_of_region (p := s.gpr .x5) (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x6).isLt)
      h.scalarScratch) h.used, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hol] at hi
    exact ⟨_, hout, contains_byte _ hi (Nat.le_of_lt (s.gpr .x1).isLt)⟩
  · intro i hi
    rw [hol] at hi
    exact Nat.le_trans h.used (out_scr h.outScratch (contains_byte _ hi (Nat.le_of_lt (s.gpr .x1).isLt)))
  · intro i hi j hj
    rw [hol] at hj
    exact (disjoint_byte_ne h.outParams hj (by rw [h.paramsLength]; exact hi)
      (Nat.le_of_lt (s.gpr .x1).isLt) (Nat.le_of_lt (s.gpr .x3).isLt)).symm
  · intro i hi j hj
    rw [hol] at hj
    exact (disjoint_byte_ne h.outScalar hj hi
      (Nat.le_of_lt (s.gpr .x1).isLt) (Nat.le_of_lt (s.gpr .x6).isLt)).symm

def DeriveABI.call {s : State} (h : DeriveABI s) : DeriveCall := ⟨h.input, s, h.pre⟩

theorem derivePreserved {s t : State} (h : DeriveABI s) (hp : DerivePost h.input s t) :
    abiPreserved s t := abiPreserved_of_keep hp.2.2.2

theorem deriveSharedPost {s t : State} (h : DeriveABI s) (hp : DerivePost h.input s t) :
    (Spec.Dsa.deriveKeyContract abi).post s t := by
  sig_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  have hol : h.input.outLen = (s.gpr .x1).toNat := h.outLength.symm
  obtain ⟨hret, hbytes, _⟩ := hp
  refine ⟨?_, ?_⟩
  · rw [hret]
    change _ = Spec.Dsa.signStatus (Spec.Dsa.deriveKeyBytes h.input.pLen h.input.qLen h.input.params h.input.x)
    cases Spec.Dsa.deriveKeyBytes h.input.pLen h.input.qLen h.input.params h.input.x <;> rfl
  · rw [← hol]
    exact hbytes

theorem deriveCorrect (M : Mont)
    (s : State) (h : (Spec.Dsa.deriveKeyContract abi).pre s) :
    ∃ trace t, Exec isa (Generate.deriveKey M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.deriveKeyContract abi).post s t := by
  have ha := deriveABI_of h
  obtain ⟨trace, t, he, hp⟩ := deriveMain_ok M ha.pre
  exact ⟨trace, t, he, derivePreserved ha hp, deriveSharedPost ha hp⟩

theorem ExecutionLayout.ext' {L₁ L₂ : ExecutionLayout} (hb : L₁.base = L₂.base) (hp : L₁.pLen = L₂.pLen)
    (hq : L₁.qLen = L₂.qLen) (hm : L₁.modulus = L₂.modulus) (hs : L₁.subgroup = L₂.subgroup)
    (hpi : L₁.pInverse = L₂.pInverse) (hqi : L₁.qInverse = L₂.qInverse) (hf : L₁.fields = L₂.fields) :
    L₁ = L₂ := by
  cases L₁
  cases L₂
  simp only at hb hp hq hm hs hpi hqi hf
  subst hb hp hq hm hs hpi hqi hf
  rfl

theorem derivePublicRelated {s₁ s₂ : State} (h₁ : DeriveABI s₁) (h₂ : DeriveABI s₂)
    (h : (Spec.Dsa.deriveKeyContract abi).pub s₁ s₂) : Two DeriveStart s₁ s₂ := by
  sig_pub [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, _, h8, h9, a0, a1, _⟩ := h
  have hpub := (List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)).1
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpub
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat h8
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat a0
  have hpb : h₁.input.params = h₂.input.params := hb
  have hpb' : h₁.input.pb = h₂.input.pb := by
    change h₁.input.params.take h₁.input.pLen = h₂.input.params.take h₂.input.pLen
    rw [hpb, hp]
  have hqb' : h₁.input.qb = h₂.input.qb := by
    change (h₁.input.params.drop h₁.input.pLen).take h₁.input.qLen =
      (h₂.input.params.drop h₂.input.pLen).take h₂.input.qLen
    rw [hpb, hp, hq]
  have hac : h₁.input.accepted = h₂.input.accepted := by
    unfold ParametersInput.accepted
    congr 1
  have hlayout : h₁.call.layout = h₂.call.layout := by
    have hf : deriveFieldValues s₁ (BitVec.ofNat 64 h₁.input.qLen) h₁.input.base h₁.input.accepted =
        deriveFieldValues s₂ (BitVec.ofNat 64 h₂.input.qLen) h₂.input.base h₂.input.accepted := by
      have hbase : h₁.input.base = h₂.input.base := a1
      funext f
      cases f <;> simp only [deriveFieldValues, hdi, hdx, h8, h9, hq, hbase, hac]
    exact ExecutionLayout.ext' a1 hp hq (congrArg Spec.Dsa.decodeBE hpb') (congrArg Spec.Dsa.decodeBE hqb')
      rfl rfl hf
  exact ⟨h₂.call, ⟨h₁.call, ⟨hlayout, hpb, hsp⟩, rfl⟩, ⟨h₂.call, ⟨rfl, rfl, rfl⟩, rfl⟩, hsp⟩

theorem deriveConstantTime (M : Mont) :
    ConstantTime isa (Spec.Dsa.deriveKeyContract abi).pre
      (Spec.Dsa.deriveKeyContract abi).pub (Generate.deriveKey M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (deriveMain_ct M _ _ _ _ _ _
    (derivePublicRelated (deriveABI_of h₁) (deriveABI_of h₂) hp) e₁ e₂).1

/-- An ordinary 1024/160 call with disjoint buffers. The all-zero domain is
allowed by the contract and rejected by the program. -/
def deriveSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 424 | .x2 => 0x2000 | .x3 => 276
    | .x4 => 128 | .x5 => 0x3000 | .x6 => 20 | .x7 => 0x8000 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10001 then 8 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x3000, 20⟩, ⟨0x10000, 8⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x8000, 16384⟩]

theorem deriveSatisfiable : ∃ s, (Spec.Dsa.deriveKeyContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
    [deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using deriveSatState

theorem derive_verified (M : Mont)
    :
    Verified target (Generate.deriveKey M.mm) (Spec.Dsa.deriveKeyContract abi) :=
  ⟨deriveCorrect M, deriveConstantTime M, deriveSatisfiable⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # AArch64 DSA key derivation for a checked domain, against its contract

`Generate.deriveChecked` is verified against `deriveKeyDomainCheckedContract`
(`Spec/Dsa/DomainChecked.lean`): `deriveKeyContract` under the precondition
that the exact domain bytes pass `checkParametersBytes`. Key generation calls
it once its domain check has returned 1. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem deriveChecked_pre {s : State} {stack : Nat}
    (h : (Spec.Dsa.deriveKeyDomainCheckedContract abi stack).pre s) :
    (Spec.Dsa.deriveKeyContract abi stack).pre s ∧
      Spec.Dsa.checkParametersBytes (s.gpr .x4).toNat (s.gpr .x6).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) = true := by
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at h
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at h
  sig_split h
  refine ⟨?_, by assumption⟩
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  sig_and_intros <;> with_reducible assumption

theorem deriveChecked_of_pre {s : State} {stack : Nat} (h : (Spec.Dsa.deriveKeyContract abi stack).pre s)
    (hc : Spec.Dsa.checkParametersBytes (s.gpr .x4).toNat (s.gpr .x6).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) = true) :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi stack).pre s := by
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at h
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at h
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem deriveCheckedCorrect (M : Mont)
    (s : State) (h : (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre s) :
    ∃ trace t, Exec isa (Generate.deriveChecked M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.deriveKeyDomainCheckedContract abi).post s t := by
  obtain ⟨hd, hc⟩ := deriveChecked_pre h
  have ha := deriveABI_of hd
  obtain ⟨trace, t, he, hp⟩ := deriveCheckedMain_ok M ha.pre hc
  refine ⟨trace, t, he, derivePreserved ha hp, ?_⟩
  have hs := deriveSharedPost ha hp
  sig_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at hs
  sig_post [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  exact hs

theorem deriveCheckedConstantTime (M : Mont) :
    ConstantTime isa (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre
      (Spec.Dsa.deriveKeyDomainCheckedContract abi).pub (Generate.deriveChecked M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (deriveCheckedMain_ct M _ _ _ _ _ _
    (derivePublicRelated (deriveABI_of (deriveChecked_pre h₁).1) (deriveABI_of (deriveChecked_pre h₂).1) hp)
      e₁ e₂).1

/-- `validatedSatKey`'s domain p‖q‖g, its first 276 bytes. -/
def validDomainWitness : List Byte := validatedSatKey.take 276

/-- `deriveSatState` with `validDomainWitness` at `0x2000`. -/
def deriveCheckedSatState : State where
  gpr := deriveSatState.gpr
  sp := deriveSatState.sp
  rd := deriveSatState.rd
  wr := deriveSatState.wr
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2114 then
    validDomainWitness[a.toNat - 0x2000]?.getD 0 else deriveSatState.mem a

theorem deriveCheckedSat_valid : Spec.Dsa.checkParametersBytes 128 20
    (Spec.Rsa.bytesAt deriveCheckedSatState.mem 0x2000 276) = true := by
  -- The memory's bytes are the list, by a lemma: evaluated, each is a walk of the list to its index.
  have hb : Spec.Rsa.bytesAt deriveCheckedSatState.mem 0x2000 276 = validDomainWitness :=
    VG.Proof.Dsa.bytesAt_of_list (lo := 0x2000) (by decide +kernel) (by decide) fun a h1 h2 => by
      have h : 0x2000 ≤ a.toNat ∧ a.toNat < 0x2114 := ⟨h1, h2⟩
      simp only [deriveCheckedSatState, h, and_self, ↓reduceIte]
  rw [hb]
  decide +kernel

theorem deriveCheckedSatisfiable : ∃ s, (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre s := by
  have ho : ∃ s, (Spec.Dsa.deriveKeyContract abi).pre s ∧ s = deriveCheckedSatState := by
    sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
      [deriveCheckedSatState, deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using deriveCheckedSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, deriveChecked_of_pre h deriveCheckedSat_valid⟩

theorem derive_checked_verified (M : Mont) :
    Verified target (Generate.deriveChecked M.mm) (Spec.Dsa.deriveKeyDomainCheckedContract abi) :=
  ⟨deriveCheckedCorrect M, deriveCheckedConstantTime M, deriveCheckedSatisfiable⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # The AArch64 DSA domain check verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem stackArgs_zero (s : State) : List.map (stackArg s) (List.range 0) = [] := rfl

structure ParametersABI (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩]
  wr : s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat * 8⟩]
  paramsScratch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x4, (s.gpr .x5).toNat * 8⟩
  paramsBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  scratchBound : (s.gpr .x4).toNat + (s.gpr .x5).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .x2).toNat (s.gpr .x3).toNat
  paramsLength : (s.gpr .x1).toNat = 2 * (s.gpr .x2).toNat + (s.gpr .x3).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .x2).toNat ≤ (s.gpr .x5).toNat

theorem parametersABI_of {s : State} (h : (Proof.Dsa.checkParametersContract abi).pre s) : ParametersABI s := by
  sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero] at h
  sig_split h
  constructor <;> with_reducible assumption

def ParametersABI.input {s : State} (h : ParametersABI s) : ParametersInput where
  base := s.gpr .x4
  pLen := (s.gpr .x2).toNat
  qLen := (s.gpr .x3).toNat
  params := Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat
  lengths := h.lengths
  paramsLength := (bytesAt_length _ _ _).trans h.paramsLength

theorem ParametersABI.used {s : State} (h : ParametersABI s) : usedBytes ≤ (s.gpr .x5).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega_using [hl, hs]

theorem ParametersABI.pre {s : State} (h : ParametersABI s) : ParametersPre h.input s := by
  have hs : Scr s (s.gpr .x4) ((s.gpr .x5).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  exact ⟨scratch_prefix hs h.used (by decide), rfl, (ofNat_toNat64 _).symm, (ofNat_toNat64 _).symm,
    source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x1).isLt) h.paramsScratch) h.used⟩

def ParametersABI.call {s : State} (h : ParametersABI s) : ParametersCall := ⟨h.input, s, h.pre⟩

theorem parametersPreserved {s t : State} (h : ParametersABI s) (hp : ParametersPost h.input s t) :
    abiPreserved s t := by
  exact abiPreserved_of_keep hp.2.2

theorem parametersSharedPost {s t : State} (h : ParametersABI s) (hp : ParametersPost h.input s t) :
    (Proof.Dsa.checkParametersContract abi).post s t := by
  sig_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
  rw [hp.1]
  change _ = if Spec.Dsa.checkParametersBytes h.input.pLen h.input.qLen h.input.params = true then 1 else 0
  cases Spec.Dsa.checkParametersBytes h.input.pLen h.input.qLen h.input.params <;> rfl

theorem parametersCorrect (M : Mont)
    (s : State) (h : (Proof.Dsa.checkParametersContract abi).pre s) :
    ∃ trace t, Exec isa (Generate.checkParameters M.mm) s trace t ∧ abiPreserved s t ∧
      (Proof.Dsa.checkParametersContract abi).post s t := by
  have ha := parametersABI_of h
  obtain ⟨trace, t, he, hp⟩ := parametersMain_ok M ha.pre
  exact ⟨trace, t, he, parametersPreserved ha hp, parametersSharedPost ha hp⟩

theorem parametersPublicRelated {s₁ s₂ : State} (h₁ : ParametersABI s₁) (h₂ : ParametersABI s₂)
    (h : (Proof.Dsa.checkParametersContract abi).pub s₁ s₂) : Two ParametersStart s₁ s₂ := by
  sig_pub [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, hcx, h8, _⟩ := h
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat hdx
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat hcx
  have hpb : h₁.input.params = h₂.input.params := hb
  have hpb' : h₁.input.pb = h₂.input.pb := by
    change h₁.input.params.take h₁.input.pLen = h₂.input.params.take h₂.input.pLen
    rw [hpb, hp]
  have hqb' : h₁.input.qb = h₂.input.qb := by
    change (h₁.input.params.drop h₁.input.pLen).take h₁.input.qLen =
      (h₂.input.params.drop h₂.input.pLen).take h₂.input.qLen
    rw [hpb, hp, hq]
  have hac : h₁.input.accepted = h₂.input.accepted := by
    unfold ParametersInput.accepted
    congr 1
  have hlayout : h₁.call.layout = h₂.call.layout := by
    change h₁.input.layout s₁ _ _ = h₂.input.layout s₂ _ _
    unfold ParametersInput.layout
    have hf : checkFieldValues s₁ h₁.input.accepted = checkFieldValues s₂ h₂.input.accepted := by
      funext f
      cases f <;> simp only [checkFieldValues, hdi, hdx, hcx, hac]
    congr 1
    · exact congrArg Spec.Dsa.decodeBE hpb'
    · exact congrArg Spec.Dsa.decodeBE hqb'
  exact ⟨h₂.call, ⟨h₁.call, ⟨hlayout, hpb⟩, rfl⟩, ⟨h₂.call, ⟨rfl, rfl⟩, rfl⟩, hsp⟩

theorem parametersConstantTime (M : Mont) :
    ConstantTime isa (Proof.Dsa.checkParametersContract abi).pre
      (Proof.Dsa.checkParametersContract abi).pub (Generate.checkParameters M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (parametersMain_ct M _ _ _ _ _ _
    (parametersPublicRelated (parametersABI_of h₁) (parametersABI_of h₂) hp) e₁ e₂).1

/-- An ordinary 1024/160 call with disjoint buffers. The all-zero domain is
allowed by the contract and rejected by the program. -/
def parametersSatState : State where
  gpr r := match r with
    | .x0 => 0x2000 | .x1 => 276 | .x2 => 128 | .x3 => 20
    | .x4 => 0x8000 | .x5 => 2048 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 276⟩]
  wr := [⟨0x8000, 16384⟩]

theorem parametersSatisfiable : ∃ s, (Proof.Dsa.checkParametersContract abi).pre s := by
  sig_implies_sat [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
    [parametersSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using parametersSatState

theorem parameters_verified (M : Mont)
    :
    Verified target (Generate.checkParameters M.mm) (Proof.Dsa.checkParametersContract abi) :=
  ⟨parametersCorrect M, parametersConstantTime M, parametersSatisfiable⟩

end VG.Proof.Dsa.AArch64
