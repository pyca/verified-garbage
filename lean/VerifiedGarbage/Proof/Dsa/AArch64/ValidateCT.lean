module

public import VerifiedGarbage.Proof.Dsa.AArch64.ValidateMain
public import VerifiedGarbage.Proof.Dsa.AArch64.ParametersCT
public import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceBridge
public import VerifiedGarbage.Proof.Dsa.AArch64.PublicScheduleCT
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.ValidateMain
meta import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceBridge
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicScheduleCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingCT
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.SizeBounds

/-! # Constant time of the AArch64 DSA domain check

Every input is public: two calls with the same pointers, lengths and domain
bytes take the same path, whatever their scratch holds. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ValidatingCall where
  input : VerifyingInput
  original : State
  pre : ValidatingPre input original

abbrev ValidatingCall.layout (c : ValidatingCall) : ExecutionLayout :=
  c.input.layout c.original c.pre.pLength c.pre.qLength

structure ValidatingAgrees (reference c : ValidatingCall) : Prop where
  layout : c.layout = reference.layout
  key : c.input.key = reference.input.key

def ValidatingStart (reference : ValidatingCall) (s : State) : Prop :=
  ∃ c : ValidatingCall, ValidatingAgrees reference c ∧ c.original = s

def ValidatingEntered (reference : ValidatingCall) (s : State) : Prop :=
  ∃ c : ValidatingCall, ValidatingAgrees reference c ∧
    ValidateEntryPost c.original c.input.base s

def ValidatingShaped (reference : ValidatingCall) (s : State) : Prop :=
  ∃ c : ValidatingCall, ValidatingAgrees reference c ∧
    VerifyingShapePost c.input c.original c.pre.pLength c.pre.qLength s

def ValidatingReady (reference : ValidatingCall) (s : State) : Prop :=
  ∃ c : ValidatingCall, ValidatingAgrees reference c ∧
    ValidatingInitialized c.input c.original c.pre.pLength c.pre.qLength s

theorem ValidatingAgrees.pLen {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.pLen = reference.input.pLen := congrArg ExecutionLayout.pLen h.layout

theorem ValidatingAgrees.qLen {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.qLen = reference.input.qLen := congrArg ExecutionLayout.qLen h.layout

theorem ValidatingAgrees.pb {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.components.p = reference.input.components.p := by
  change c.input.key.take c.input.pLen = reference.input.key.take reference.input.pLen
  rw [h.key, h.pLen]

theorem ValidatingAgrees.qb {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.components.q = reference.input.components.q := by
  change (c.input.key.drop c.input.pLen).take c.input.qLen =
    (reference.input.key.drop reference.input.pLen).take reference.input.qLen
  rw [h.key, h.pLen, h.qLen]

theorem ValidatingAgrees.accepted {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.accepted = reference.input.accepted := by
  unfold VerifyingInput.accepted
  congr 1
  · exact h.pb
  · exact h.qb

theorem validateEntry_ct : RelCT isa (Two (fun B : Addr => fun s => s.gpr .x4 = B))
    (.block Prevalidated.validateEntry) (fun _ _ => True) :=
  two_taint [.x4] (pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)) (by taint_decide)

theorem validatingEntered_ct : RelCT isa (Two ValidatingStart) (.block Prevalidated.validateEntry)
    (Two ValidatingEntered) := by
  refine two_post (two_map (fun c : ValidatingCall => c.layout.base) ?_ validateEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact c.pre.base.trans (congrArg ExecutionLayout.base ha.layout)
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact WP.mono (validateEntry_ok c.pre.scratch c.pre.base (by decide)) fun t ht => ⟨c, ha, ht⟩

def ValidatingCall.shape (c : ValidatingCall) : ShapePublic where
  base := c.layout.base
  extent := usedBytes
  pPointer := c.layout.fields .p
  qPointer := c.layout.fields .q
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  digestLen := 0
  extentBound := by decide
  pPositive := by rw [c.input.components.pLength]; have := c.layout.widths; change 0 < c.layout.pLen; omega
  qPositive := by rw [c.input.components.qLength]; have := c.layout.widths; change 0 < c.layout.qLen; omega
  pBound := by rw [c.input.components.pLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega
  qBound := by rw [c.input.components.qLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega
  digestBound := by decide

theorem ValidatingAgrees.shape {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.shape = reference.shape := by
  unfold ValidatingCall.shape
  congr 1
  · exact congrArg ExecutionLayout.base h.layout
  · exact congrArg (fun L => L.fields .p) h.layout
  · exact congrArg (fun L => L.fields .q) h.layout
  · exact h.pb
  · exact h.qb

theorem ValidatingEntered.context {reference : ValidatingCall} {s : State} (h : ValidatingEntered reference s) :
    ShapeContext reference.shape s := by
  obtain ⟨c, ha, he⟩ := h
  rw [← ha.shape]
  have hf : InScr c.input.base usedBytes c.original.mem s.mem := InScr.of_outside he.frame (by decide)
  have hkey := c.pre.keySource.congrK hf he.keep
  have hps : Src s c.input.base usedBytes (c.layout.fields .p) c.input.components.p := source_take hkey
  have hqs : Src s c.input.base usedBytes (c.layout.fields .q) c.input.components.q := by
    change Src s c.input.base usedBytes (c.original.gpr .x0 + c.original.gpr .x2) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega)
  refine ⟨c.pre.scratch.congr he.keep.wr, he.base, he.fields .p (by decide) (by decide),
    he.fields .q (by decide) (by decide), ?_, ?_, he.fields .digestLen (by decide) (by decide), hps, hqs⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.components.p.length
    rw [c.input.components.pLength]
    exact (he.fields .pLen (by decide) (by decide)).trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.components.q.length
    rw [c.input.components.qLength]
    exact (he.fields .qLen (by decide) (by decide)).trans c.pre.qLength

theorem validatingShape_ct : RelCT isa (Two ValidatingStart)
    (.seq (.block Prevalidated.validateEntry) Checks.domainShape) (Two ValidatingShaped) := by
  refine two_post (RelCT.seq validatingEntered_ct
    (two_map ValidatingCall.shape (fun _ _ h => h.context) domainShape_ct)) ?_
  intro reference s ⟨c, ha, hs⟩
  subst s
  exact WP.mono (validatingShape_ok c.pre) fun t ht => ⟨c, ha, ht⟩

theorem ValidatingShaped.branch {reference : ValidatingCall} {s : State} (h : ValidatingShaped reference s) :
    eval (.zero .x .x3) s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change some (s.gpr .x3 == (0#64)) = _
  rw [hs.branch, ha.accepted]

theorem ValidatingShaped.x0 {reference : ValidatingCall} {s : State} (h : ValidatingShaped reference s) :
    s.gpr .x0 = reference.layout.base := by
  obtain ⟨c, ha, hs⟩ := h
  exact hs.x0.trans (congrArg ExecutionLayout.base ha.layout)

def ValidatingCall.initialization (c : ValidatingCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  pLength := c.input.components.pLength
  qLength := c.input.components.qLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem ValidatingShaped.initialization {reference : ValidatingCall} {s : State}
    (h : ValidatingShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .x0 = c.layout.base := hs.x0
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  have hkey := c.pre.keySource.congrK hs.frame hs.keep
  have hps' : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.components.p := source_take hkey
  have hqs' : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.components.q := by
    change Src s c.input.base usedBytes (c.original.gpr .x0 + c.original.gpr .x2) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega)
  rw [hag.layout] at hf hr hscr hps' hqs'
  rw [hag.pb] at hps'
  rw [hag.qb] at hqs'
  exact ⟨hscr, hr, hf, hps', hqs'⟩

abbrev AcceptedValidatingCall := {c : ValidatingCall // c.input.accepted = true}

theorem validatingWorkspaces_ct : RelCT isa (Two (fun c : AcceptedValidatingCall => ValidatingShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedValidatingCall => ValidatingReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedValidatingCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (validatingInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

/-- The domain's operands, as the schedule reads them. -/
def validatingInputs (p : SchedulePublic) : List (Operand × Nat) :=
  [(Core.publicValue, p.layout.pLen), (⟨.input .q, .qLen⟩, p.layout.qLen), (Core.generator, p.layout.pLen)]

theorem validatingInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ validatingInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [validatingInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · simp [Core.publicValue, stablePointer]
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · simp [Core.generator, stablePointer]

def ValidatingCall.schedule (c : ValidatingCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
  layout := c.layout.withInverses pi qi
  digestLen := 0
  pGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).1
  qGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).2.1
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2
  pFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.components.p
    rw [c.input.components.pLength] at h
    exact Nat.le_of_lt h
  qFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.components.q
    rw [c.input.components.qLength] at h
    exact Nat.le_of_lt h
  digestBound := by decide

theorem ValidatingReady.body {reference : ValidatingCall} {s : State} (ha : reference.input.accepted = true)
    (h : ValidatingReady reference s) : ∃ pi qi, PublicKeyPre validatingInputs (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, _⟩ := h
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  change Ready (c.layout.withInverses pi qi) s at hr
  change (OperandBytes s c.layout.base usedBytes Core.generator c.input.components.g ∧
    OperandBytes s c.layout.base usedBytes Core.publicValue c.input.components.y ∧
    OperandBytes s c.layout.base usedBytes ⟨.input .q, .qLen⟩ c.input.components.q) at ho
  rw [hag.layout] at hr ho hmask
  have hgl : c.input.components.g.length = reference.layout.pLen := c.input.components.gLength.trans hag.pLen
  have hyl : c.input.components.y.length = reference.layout.pLen := c.input.components.yLength.trans hag.pLen
  have hql : c.input.components.q.length = reference.layout.qLen := c.input.components.qLength.trans hag.qLen
  refine ⟨pi, qi, ⟨hr, ?_, ⟨true, hmask⟩⟩, c.input.components.q, ho.2.2, hql, ?_⟩
  · intro a ha
    simp only [validatingInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨_, ho.2.1, hyl⟩
    · exact ⟨_, ho.2.2, hql⟩
    · exact ⟨_, ho.1, hgl⟩
  · change Spec.Dsa.decodeBE c.input.components.q = Spec.Dsa.decodeBE reference.input.components.q
    rw [hag.qb]

theorem validatingReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedValidatingCall => ValidatingReady c.val) s₁ s₂) :
    Two (PublicKeyPre validatingInputs) s₁ s₂ := by
  obtain ⟨reference, h₁, h₂, hsp⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1.1 h₂.1.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂, hsp⟩

theorem validatingBody_ct (M : Mont) : RelCT isa (Two (PublicKeyPre validatingInputs))
    (seqs [Checks.publicKey M.mm, .block SignVerify.result]) (fun _ _ => True) := by
  have h1 := publicKey_ct M validatingInputs (fun p => validatingInputs_stable p)
    (by intro p; simp [validatingInputs]) (by intro p; simp [validatingInputs])
    (by intro p; simp [validatingInputs])
  unfold seqs
  refine RelCT.seq h1 ?_
  exact two_map (fun p => p.layout.base) (fun _ _ h => h.1.parent.x0) result_ct

theorem validatingSuccess_ct (M : Mont) :
    RelCT isa (Two (fun c : AcceptedValidatingCall => ValidatingShaped c.val))
      (seqs [SignVerify.workspaces, Checks.publicKey M.mm, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq validatingWorkspaces_ct ?_
  exact (validatingBody_ct M).mono (fun _ _ h => validatingReady_related h) (fun _ _ h => h)

theorem validatingMain_ct (M : Mont) :
    RelCT isa (Two ValidatingStart) (Prevalidated.validate M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq validatingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂, hsp⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map (fun c : ValidatingCall => c.layout.base) (fun _ _ h => h.x0) verifyFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (validatingSuccess_ct M).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂, hsp⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval (.zero .x .x3) s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64
