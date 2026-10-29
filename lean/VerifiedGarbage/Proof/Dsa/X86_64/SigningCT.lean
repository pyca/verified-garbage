module

public import VerifiedGarbage.Proof.Dsa.X86_64.FailureCT
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningPublic

import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
import VerifiedGarbage.Proof.Dsa.X86_64.BodyCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.SizeBounds
/-! # Constant time of the complete signing entry point -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/SigningShapeCT.lean`, which only this module imported.
section

/-! # Constant time of signing argument capture and domain validation -/

section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem signingEntered_ct : RelCT isa (Two SigningStart) (.block SignVerify.signEntry) (Two SigningEntered) := by
  refine two_post (two_map (fun c : SigningCall => (c.layout.base, c.original.gpr .rsp)) ?_ signEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    have hb : c.input.base = reference.layout.base := congrArg ExecutionLayout.base ha.layout
    refine ⟨ha.stack, ?_, ?_⟩
    · rw [← ha.stack, ← hb]
      exact c.pre.base
    · rw [← ha.stack]
      exact c.pre.stackRead 4 (by decide) (by decide)
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact WP.mono (signEntry_ok c.pre.scratch rfl (by decide) c.pre.stackRead c.pre.stackSeparate
      c.pre.qLength c.pre.digestPointer c.pre.digestLength c.pre.base) fun t ht => ⟨c, ha, ht⟩

theorem signingShape_ct : RelCT isa (Two SigningStart)
    (.seq (.block SignVerify.signEntry) Checks.domainShape) (Two SigningShaped) := by
  refine two_post (RelCT.seq signingEntered_ct
    (two_map SigningCall.shape (fun _ _ h => h.context) domainShape_ct)) ?_
  intro reference s ⟨c, ha, hs⟩
  subst s
  exact WP.mono (signingShape_ok c.pre) fun t ht => ⟨c, ha, ht⟩

def SigningCall.initialization (c : SigningCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  pLength := c.input.components.pLength
  qLength := c.input.components.qLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem SigningShaped.initialization {reference : SigningCall} {s : State}
    (h : SigningShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .rdi = c.layout.base := hs.rdi
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  have hkey := c.pre.keySource.congrK hs.frame hs.keep
  have hps : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.components.p := source_take hkey
  have hqs : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.components.q := by
    change Src s c.input.base usedBytes (c.original.gpr .rdx + c.original.gpr .r8) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega)
  rw [hag.layout] at hf hr hscr hps hqs
  rw [hag.pBytes] at hps
  rw [hag.qBytes] at hqs
  exact ⟨hscr, hr, hf, hps, hqs⟩

abbrev AcceptedSigningCall := {c : SigningCall // c.input.accepted = true}

theorem signingWorkspaces_ct : RelCT isa (Two (fun c : AcceptedSigningCall => SigningShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedSigningCall => SigningReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedSigningCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (signingInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

end VG.Proof.Dsa.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/SigningReadyCT.lean`, which only this module imported.
section

/-! # The public schedule after independent signing-workspace initialization -/

section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def SigningCall.schedule (c : SigningCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
  layout := c.layout.withInverses pi qi
  digestLen := c.input.prefixLength
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
  digestBound := Nat.lt_of_le_of_lt (Nat.min_le_left _ _) c.input.digestBound

theorem SigningAgrees.prefixLength {reference c : SigningCall} (h : SigningAgrees reference c) :
    c.input.prefixLength = reference.input.prefixLength := by
  unfold SigningInput.prefixLength
  rw [h.digestLength, h.qBytes]

theorem SigningReady.body {reference : SigningCall} {s : State} (ha : reference.input.accepted = true)
    (h : SigningReady reference s) : ∃ pi qi, SigningBodyPre (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, _, hk⟩ := h
  have hw : ∀ i < 2 * c.layout.qLen, InRegions s.wr (c.layout.fields .out + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hk.2.2]
    exact c.pre.writable i hi
  have hsep : ∀ i < 2 * c.layout.qLen,
      usedBytes ≤ ofs c.layout.base (c.layout.fields .out + BitVec.ofNat 64 i) := c.pre.separate
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  change Ready (c.layout.withInverses pi qi) s at hr
  change SigningOperands (c.layout.withInverses pi qi) c.input.values c.input.components.y c.input.components.q s at ho
  rw [hag.layout] at hr ho hw hsep hmask
  refine ⟨pi, qi, hr, ⟨c.input.values, c.input.components.y, c.input.components.q, ho, ?_⟩,
    ⟨true, hmask⟩, hw, hsep⟩
  change (c.input.digest.take _).length = reference.input.prefixLength
  rw [List.length_take, Nat.min_comm]
  exact hag.prefixLength

theorem signingReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedSigningCall => SigningReady c.val) s₁ s₂) : Two SigningBodyPre s₁ s₂ := by
  obtain ⟨reference, h₁, h₂⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1 h₂.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂⟩

theorem signingSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedSigningCall => SigningShaped c.val))
      (seqs [SignVerify.workspaces, Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
        Core.sign Sq.mm M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true,
        SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq signingWorkspaces_ct ?_
  apply RelCT.seqs_append (a := [Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
    Core.sign Sq.mm M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true])
    (b := [SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
    (by simp) (by simp)
  exact (signBody_ct M Sq).mono (fun _ _ h => signingReady_related h) (fun _ _ h => h)

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem SigningShaped.branch {reference : SigningCall} {s : State} (h : SigningShaped reference s) :
    eval .e s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change s.zf = _
  rw [hs.branch, ha.accepted]

def SigningCall.failure (c : SigningCall) : FailurePublic := ⟨c.layout.base, c.layout.fields .out, c.layout.qLen⟩

theorem SigningShaped.failure {reference : SigningCall} {s : State} (h : SigningShaped reference s) :
    FailurePre reference.failure s := by
  obtain ⟨c, ha, hs⟩ := h
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  have hr : s.gpr .rdi = c.layout.base := hs.rdi
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  rw [ha.layout] at hscr hr hf
  exact ⟨usedBytes, hscr, by decide, hr, hf .out, (hf .qLen).trans reference.layout.qLength⟩

theorem signingMain_ct (M : Mont) (Sq : MontS) : RelCT isa (Two SigningStart) (SignVerify.sign Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq signingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map SigningCall.failure (fun _ _ h => h.failure) signFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (signingSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64
