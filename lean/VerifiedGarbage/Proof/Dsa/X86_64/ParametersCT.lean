module

public import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
public import VerifiedGarbage.Proof.Dsa.X86_64.PublicScheduleCT
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicScheduleCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
public import VerifiedGarbage.Proof.Dsa.SizeBounds

/-! # Constant time of the x86-64 DSA domain check

Every input is public: two calls with the same pointers, lengths and domain
bytes take the same path, whatever their scratch holds. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure ParametersCall where
  input : ParametersInput
  original : State
  pre : ParametersPre input original

abbrev ParametersCall.layout (c : ParametersCall) : ExecutionLayout :=
  c.input.layout c.original c.pre.pLength c.pre.qLength

structure ParametersAgrees (reference c : ParametersCall) : Prop where
  layout : c.layout = reference.layout
  params : c.input.params = reference.input.params

def ParametersStart (reference : ParametersCall) (s : State) : Prop :=
  ∃ c : ParametersCall, ParametersAgrees reference c ∧ c.original = s

def ParametersEntered (reference : ParametersCall) (s : State) : Prop :=
  ∃ c : ParametersCall, ParametersAgrees reference c ∧
    KeygenEntryPost c.original c.input.base (checkFieldValues c.original true) s

def ParametersShaped (reference : ParametersCall) (s : State) : Prop :=
  ∃ c : ParametersCall, ParametersAgrees reference c ∧
    ParametersShapePost c.input c.original c.pre.pLength c.pre.qLength s

def ParametersReady (reference : ParametersCall) (s : State) : Prop :=
  ∃ c : ParametersCall, ParametersAgrees reference c ∧
    ParametersInitialized c.input c.original c.pre.pLength c.pre.qLength s

theorem ParametersAgrees.pLen {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.pLen = reference.input.pLen := congrArg ExecutionLayout.pLen h.layout

theorem ParametersAgrees.qLen {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.qLen = reference.input.qLen := congrArg ExecutionLayout.qLen h.layout

theorem ParametersAgrees.pb {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.pb = reference.input.pb := by
  rw [ParametersInput.pb, ParametersInput.pb, h.params, h.pLen]

theorem ParametersAgrees.qb {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.qb = reference.input.qb := by
  rw [ParametersInput.qb, ParametersInput.qb, h.params, h.pLen, h.qLen]

theorem ParametersAgrees.gb {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.gb = reference.input.gb := by
  rw [ParametersInput.gb, ParametersInput.gb, h.params, h.pLen, h.qLen]

theorem ParametersAgrees.accepted {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.accepted = reference.input.accepted := by
  unfold ParametersInput.accepted
  congr 1
  · exact h.pb
  · exact h.qb

theorem checkEntry_ct : RelCT isa (Two (fun B : Addr => fun s => s.gpr .r8 = B))
    (.block Generate.checkEntry) (fun _ _ => True) :=
  two_taint [.r8] (pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)) (by taint_decide)

theorem parametersEntered_ct : RelCT isa (Two ParametersStart) (.block Generate.checkEntry)
    (Two ParametersEntered) := by
  refine two_post (two_map (fun c : ParametersCall => c.layout.base) ?_ checkEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact c.pre.base.trans (congrArg ExecutionLayout.base ha.layout)
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact WP.mono (checkEntry_ok c.pre.scratch c.pre.base) fun t ht => ⟨c, ha, ht⟩

def ParametersCall.shape (c : ParametersCall) : ShapePublic where
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
  pBound := by rw [c.input.pbLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega
  qBound := by rw [c.input.qbLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega
  digestBound := by decide

theorem ParametersAgrees.shape {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.shape = reference.shape := by
  unfold ParametersCall.shape
  congr 1
  · exact congrArg ExecutionLayout.base h.layout
  · exact congrArg (fun L => L.fields .p) h.layout
  · exact congrArg (fun L => L.fields .q) h.layout
  · exact h.pb
  · exact h.qb

theorem ParametersEntered.context {reference : ParametersCall} {s : State} (h : ParametersEntered reference s) :
    ShapeContext reference.shape s := by
  obtain ⟨c, ha, he⟩ := h
  rw [← ha.shape]
  have hf : InScr c.input.base usedBytes c.original.mem s.mem := InScr.of_outside he.frame (by decide)
  obtain ⟨hps, hqs, _⟩ := c.pre.sources hf (he.keep.mono (by decide))
  refine ⟨c.pre.scratch.congr he.keep.2.2, he.base, he.fields .p (by decide) (by decide),
    he.fields .q (by decide) (by decide), ?_, ?_, he.fields .digestLen (by decide) (by decide), hps, hqs⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.pb.length
    rw [c.input.pbLength]
    exact (he.fields .pLen (by decide) (by decide)).trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.qb.length
    rw [c.input.qbLength]
    exact (he.fields .qLen (by decide) (by decide)).trans c.pre.qLength

theorem parametersShape_ct : RelCT isa (Two ParametersStart)
    (.seq (.block Generate.checkEntry) Checks.domainShape) (Two ParametersShaped) := by
  refine two_post (RelCT.seq parametersEntered_ct
    (two_map ParametersCall.shape (fun _ _ h => h.context) domainShape_ct)) ?_
  intro reference s ⟨c, ha, hs⟩
  subst s
  exact WP.mono (parametersShape_ok c.pre) fun t ht => ⟨c, ha, ht⟩

theorem ParametersShaped.branch {reference : ParametersCall} {s : State} (h : ParametersShaped reference s) :
    eval .e s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change s.zf = _
  rw [hs.branch, ha.accepted]

theorem ParametersShaped.rdi {reference : ParametersCall} {s : State} (h : ParametersShaped reference s) :
    s.gpr .rdi = reference.layout.base := by
  obtain ⟨c, ha, hs⟩ := h
  exact hs.rdi.trans (congrArg ExecutionLayout.base ha.layout)

def ParametersCall.initialization (c : ParametersCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.pb
  qBytes := c.input.qb
  pLength := c.input.pbLength
  qLength := c.input.qbLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem ParametersShaped.initialization {reference : ParametersCall} {s : State}
    (h : ParametersShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .rdi = c.layout.base := hs.rdi
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  obtain ⟨hps, hqs, _⟩ := c.pre.sources hs.frame hs.keep
  have hps' : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.pb := hps
  have hqs' : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.qb := hqs
  rw [hag.layout] at hf hr hscr hps' hqs'
  rw [hag.pb] at hps'
  rw [hag.qb] at hqs'
  exact ⟨hscr, hr, hf, hps', hqs'⟩

abbrev AcceptedParametersCall := {c : ParametersCall // c.input.accepted = true}

theorem parametersWorkspaces_ct : RelCT isa (Two (fun c : AcceptedParametersCall => ParametersShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedParametersCall => ParametersReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedParametersCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (parametersInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

/-- The domain's operands, as the schedule reads them. -/
def parametersInputs (p : SchedulePublic) : List (Operand × Nat) :=
  [(Core.publicValue, p.layout.pLen), (⟨.input .q, .qLen⟩, p.layout.qLen), (Core.generator, p.layout.pLen)]

theorem parametersInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ parametersInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [parametersInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · simp [Core.publicValue, stablePointer]
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · simp [Core.generator, stablePointer]

def ParametersCall.schedule (c : ParametersCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
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

theorem ParametersReady.body {reference : ParametersCall} {s : State} (ha : reference.input.accepted = true)
    (h : ParametersReady reference s) : ∃ pi qi, PublicKeyPre parametersInputs (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, _, _⟩ := h
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  change Ready (c.layout.withInverses pi qi) s at hr
  change ParametersOperands (c.layout.withInverses pi qi) c.input s at ho
  rw [hag.layout] at hr ho hmask
  have hgl : c.input.gb.length = reference.layout.pLen := c.input.gbLength.trans hag.pLen
  have hql : c.input.qb.length = reference.layout.qLen := c.input.qbLength.trans hag.qLen
  refine ⟨pi, qi, ⟨hr, ?_, ⟨true, hmask⟩⟩, c.input.qb, ho.subgroup, hql, ?_⟩
  · intro a ha
    simp only [parametersInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨_, ho.publicValue, hgl⟩
    · exact ⟨_, ho.subgroup, hql⟩
    · exact ⟨_, ho.generator, hgl⟩
  · change Spec.Dsa.decodeBE c.input.qb = Spec.Dsa.decodeBE reference.input.qb
    rw [hag.qb]

theorem parametersReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedParametersCall => ParametersReady c.val) s₁ s₂) :
    Two (PublicKeyPre parametersInputs) s₁ s₂ := by
  obtain ⟨reference, h₁, h₂⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1.1 h₂.1.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂⟩

theorem parametersBody_ct (M : Mont) (Sq : MontS) : RelCT isa (Two (PublicKeyPre parametersInputs))
    (seqs [Checks.signingKey Sq.mm M.mm, .block SignVerify.result]) (fun _ _ => True) := by
  have h1 := signingKey_ct M Sq parametersInputs (fun p => parametersInputs_stable p)
    (by intro p; simp [parametersInputs]) (by intro p; simp [parametersInputs])
    (by intro p; simp [parametersInputs])
  unfold seqs
  refine RelCT.seq h1 ?_
  exact two_map (fun p => p.layout.base) (fun _ _ h => h.1.parent.rdi) result_ct

theorem parametersSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedParametersCall => ParametersShaped c.val))
      (seqs [SignVerify.workspaces, Checks.signingKey Sq.mm M.mm, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq parametersWorkspaces_ct ?_
  exact (parametersBody_ct M Sq).mono (fun _ _ h => parametersReady_related h) (fun _ _ h => h)

theorem parametersMain_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two ParametersStart) (Generate.checkParameters Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq parametersShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map (fun c : ParametersCall => c.layout.base) (fun _ _ h => h.rdi) verifyFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (parametersSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64
