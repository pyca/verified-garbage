module

public import VerifiedGarbage.Proof.Dsa.X86_64.ValidatePrivate
public import VerifiedGarbage.Proof.Dsa.X86_64.PublicScheduleCT
public import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.X86_64.PrivateKeyCT
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.X86_64.ValidatePrivate
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicScheduleCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PrivateKeyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant time of the x86-64 DSA private-key validator

Two calls with the same pointers, lengths and public key components take
the same path, whatever their private scalars and scratch hold. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure PrivateCall where
  input : PrivateInput
  original : State
  pre : PrivatePre input original

abbrev PrivateCall.layout (c : PrivateCall) : ExecutionLayout :=
  c.input.layout c.original c.pre.pLength c.pre.qLength

structure PrivateAgrees (reference c : PrivateCall) : Prop where
  layout : c.layout = reference.layout
  pBytes : c.input.components.p = reference.input.components.p
  qBytes : c.input.components.q = reference.input.components.q

def PrivateStart (reference : PrivateCall) (s : State) : Prop :=
  ∃ c : PrivateCall, PrivateAgrees reference c ∧ c.original = s

def PrivateEntered (reference : PrivateCall) (s : State) : Prop :=
  ∃ c : PrivateCall, PrivateAgrees reference c ∧
    KeygenEntryPost c.original c.input.base (privateFieldValues c.original true) s

def PrivateShaped (reference : PrivateCall) (s : State) : Prop :=
  ∃ c : PrivateCall, PrivateAgrees reference c ∧
    PrivateShapePost c.input c.original c.pre.pLength c.pre.qLength s

def PrivateReady (reference : PrivateCall) (s : State) : Prop :=
  ∃ c : PrivateCall, PrivateAgrees reference c ∧
    PrivateInitialized c.input c.original c.pre.pLength c.pre.qLength s

theorem PrivateAgrees.pLen {reference c : PrivateCall} (h : PrivateAgrees reference c) :
    c.input.pLen = reference.input.pLen := congrArg ExecutionLayout.pLen h.layout

theorem PrivateAgrees.qLen {reference c : PrivateCall} (h : PrivateAgrees reference c) :
    c.input.qLen = reference.input.qLen := congrArg ExecutionLayout.qLen h.layout

theorem PrivateAgrees.accepted {reference c : PrivateCall} (h : PrivateAgrees reference c) :
    c.input.accepted = reference.input.accepted := by
  unfold PrivateInput.accepted
  congr 1
  · exact h.pBytes
  · exact h.qBytes

theorem privateEntry_ct : RelCT isa (Two (fun B : Addr => fun s => s.gpr .r8 = B))
    (.block PrevalidatedSign.validateEntry) (fun _ _ => True) :=
  two_taint [.r8] (pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)) (by taint_decide)

theorem privateEntered_ct : RelCT isa (Two PrivateStart) (.block PrevalidatedSign.validateEntry)
    (Two PrivateEntered) := by
  refine two_post (two_map (fun c : PrivateCall => c.layout.base) ?_ privateEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact c.pre.base.trans (congrArg ExecutionLayout.base ha.layout)
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact WP.mono (privateEntry_ok c.pre.scratch c.pre.base) fun t ht => ⟨c, ha, ht⟩

def PrivateCall.shape (c : PrivateCall) : ShapePublic where
  base := c.layout.base
  extent := usedBytes
  pPointer := c.layout.fields .p
  qPointer := c.layout.fields .q
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  digestLen := 0
  extentBound := by decide
  pPositive := c.input.pPositive
  qPositive := c.input.qPositive
  pBound := by
    rw [c.input.components.pLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega
  qBound := by
    rw [c.input.components.qLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega
  digestBound := by decide

theorem PrivateAgrees.shape {reference c : PrivateCall} (h : PrivateAgrees reference c) :
    c.shape = reference.shape := by
  unfold PrivateCall.shape
  congr 1
  · exact congrArg ExecutionLayout.base h.layout
  · exact congrArg (fun L => L.fields .p) h.layout
  · exact congrArg (fun L => L.fields .q) h.layout
  · exact h.pBytes
  · exact h.qBytes

theorem PrivateEntered.context {reference : PrivateCall} {s : State} (h : PrivateEntered reference s) :
    ShapeContext reference.shape s := by
  obtain ⟨c, ha, he⟩ := h
  rw [← ha.shape]
  have hf : InScr c.input.base usedBytes c.original.mem s.mem := InScr.of_outside he.frame (by decide)
  obtain ⟨hps, hqs, _⟩ := c.pre.sources hf (he.keep.mono (by decide))
  refine ⟨c.pre.scratch.congr he.keep.2.2, he.base, he.fields .p (by decide) (by decide),
    he.fields .q (by decide) (by decide), ?_, ?_, he.fields .digestLen (by decide) (by decide), hps, hqs⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.components.p.length
    rw [c.input.components.pLength]
    exact (he.fields .pLen (by decide) (by decide)).trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.components.q.length
    rw [c.input.components.qLength]
    exact (he.fields .qLen (by decide) (by decide)).trans c.pre.qLength

theorem privateShape_ct : RelCT isa (Two PrivateStart)
    (.seq (.block PrevalidatedSign.validateEntry) Checks.domainShape) (Two PrivateShaped) := by
  refine two_post (RelCT.seq privateEntered_ct
    (two_map PrivateCall.shape (fun _ _ h => h.context) domainShape_ct)) ?_
  intro reference s ⟨c, ha, hs⟩
  subst s
  exact WP.mono (privateShape_ok c.pre) fun t ht => ⟨c, ha, ht⟩

theorem PrivateShaped.branch {reference : PrivateCall} {s : State} (h : PrivateShaped reference s) :
    eval .e s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change s.zf = _
  rw [hs.branch, ha.accepted]

theorem PrivateShaped.rdi {reference : PrivateCall} {s : State} (h : PrivateShaped reference s) :
    s.gpr .rdi = reference.layout.base := by
  obtain ⟨c, ha, hs⟩ := h
  exact hs.rdi.trans (congrArg ExecutionLayout.base ha.layout)

def PrivateCall.initialization (c : PrivateCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  pLength := c.input.components.pLength
  qLength := c.input.components.qLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem PrivateShaped.initialization {reference : PrivateCall} {s : State}
    (h : PrivateShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .rdi = c.layout.base := hs.rdi
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  obtain ⟨hps, hqs, _⟩ := c.pre.sources hs.frame hs.keep
  have hps' : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.components.p := hps
  have hqs' : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.components.q := hqs
  rw [hag.layout] at hf hr hscr hps' hqs'
  rw [hag.pBytes] at hps'
  rw [hag.qBytes] at hqs'
  exact ⟨hscr, hr, hf, hps', hqs'⟩

abbrev AcceptedPrivateCall := {c : PrivateCall // c.input.accepted = true}

theorem privateWorkspaces_ct : RelCT isa (Two (fun c : AcceptedPrivateCall => PrivateShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedPrivateCall => PrivateReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedPrivateCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (privateInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

/-- The key's operands, as the schedule reads them. -/
def privateInputs (p : SchedulePublic) : List (Operand × Nat) :=
  [(Core.publicValue, p.layout.pLen), (⟨.input .q, .qLen⟩, p.layout.qLen), (Core.generator, p.layout.pLen),
    (Core.privateScalar, p.layout.qLen), (Core.nonce, p.layout.qLen)]

theorem privateInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ privateInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [privateInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · simp [Core.publicValue, stablePointer]
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · simp [Core.generator, stablePointer]
  · simp [Core.privateScalar, stablePointer]
  · simp [Core.nonce, stablePointer]

def PrivateCall.schedule (c : PrivateCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
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

theorem PrivateReady.body {reference : PrivateCall} {s : State} (ha : reference.input.accepted = true)
    (h : PrivateReady reference s) : ∃ pi qi, PublicKeyPre privateInputs (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, _, _⟩ := h
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  change Ready (c.layout.withInverses pi qi) s at hr
  change PrivateOperands (c.layout.withInverses pi qi) c.input s at ho
  rw [hag.layout] at hr ho hmask
  have hpl (bs : List Byte) (hb : bs.length = c.input.pLen) : bs.length = reference.layout.pLen :=
    hb.trans hag.pLen
  have hql (bs : List Byte) (hb : bs.length = c.input.qLen) : bs.length = reference.layout.qLen :=
    hb.trans hag.qLen
  refine ⟨pi, qi, ⟨hr, ?_, ⟨true, hmask⟩⟩, c.input.components.q, ho.subgroup,
    hql _ c.input.components.qLength, ?_⟩
  · intro a ha
    simp only [privateInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, ho.publicValue, hpl _ c.input.components.yLength⟩
    · exact ⟨_, ho.subgroup, hql _ c.input.components.qLength⟩
    · exact ⟨_, ho.generator, hpl _ c.input.components.gLength⟩
    · exact ⟨_, ho.privateScalar, hql _ c.input.xLength⟩
    · exact ⟨_, ho.nonce, hql _ c.input.xLength⟩
  · change Spec.Dsa.decodeBE c.input.components.q = Spec.Dsa.decodeBE reference.input.components.q
    rw [hag.qBytes]

theorem privateReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedPrivateCall => PrivateReady c.val) s₁ s₂) :
    Two (PublicKeyPre privateInputs) s₁ s₂ := by
  obtain ⟨reference, h₁, h₂⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1.1 h₂.1.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂⟩

theorem privateBody_ct (M : Mont) (Sq : MontS) : RelCT isa (Two (PublicKeyPre privateInputs))
    (seqs [Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm, .block SignVerify.result])
    (fun _ _ => True) := by
  have h1 := signingKey_ct M Sq privateInputs (fun p => privateInputs_stable p)
    (by intro p; simp [privateInputs]) (by intro p; simp [privateInputs])
    (by intro p; simp [privateInputs])
  have h2 := privateKey_ct M Sq privateInputs (fun p => privateInputs_stable p)
    (by intro p; simp [privateInputs]) (by intro p; simp [privateInputs])
    (by intro p; simp [privateInputs]) (by intro p; simp [privateInputs])
  unfold seqs
  refine RelCT.seq h1 (RelCT.seq h2 ?_)
  exact two_map (fun p => p.layout.base) (fun _ _ h => h.1.parent.rdi) result_ct

theorem privateSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedPrivateCall => PrivateShaped c.val))
      (seqs [SignVerify.workspaces, Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
        .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq privateWorkspaces_ct ?_
  exact (privateBody_ct M Sq).mono (fun _ _ h => privateReady_related h) (fun _ _ h => h)

theorem privateMain_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two PrivateStart) (PrevalidatedSign.validate Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq privateShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map (fun c : PrivateCall => c.layout.base) (fun _ _ h => h.rdi) verifyFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (privateSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64
