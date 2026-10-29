module

public import VerifiedGarbage.Proof.Dsa.X86_64.BodyCT
public import VerifiedGarbage.Proof.Dsa.SizeBounds
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingPublic

import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
/-! # The public schedule after independent verifying-workspace initialization -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/VerifyingShapeCT.lean`, which only this module imported.
section

/-! # Constant time of verifying argument capture and domain validation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem verifyingEntered_ct : RelCT isa (Two VerifyingStart) (.block SignVerify.verifyEntry) (Two VerifyingEntered) := by
  refine two_post (two_map (fun c : VerifyingCall => (c.layout.base, c.original.gpr .rsp)) ?_ verifyEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    have hb : c.input.base = reference.layout.base := congrArg ExecutionLayout.base ha.layout
    refine ⟨ha.stack, ?_, ?_⟩
    · rw [← ha.stack, ← hb]
      exact c.pre.base
    · rw [← ha.stack]
      exact c.pre.stackRead 3 (by decide) (by decide)
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact WP.mono (verifyEntry_ok c.pre.scratch rfl (by decide) c.pre.stackRead c.pre.stackSeparate
      c.pre.digestPointer c.pre.digestLength c.pre.base) fun t ht => ⟨c, ha, ht⟩

theorem verifyingShape_ct : RelCT isa (Two VerifyingStart)
    (.seq (.block SignVerify.verifyEntry) Checks.domainShape) (Two VerifyingShaped) := by
  refine two_post (RelCT.seq verifyingEntered_ct
    (two_map VerifyingCall.shape (fun _ _ h => h.context) domainShape_ct)) ?_
  intro reference s ⟨c, ha, hs⟩
  subst s
  exact WP.mono (verifyingShape_ok c.pre) fun t ht => ⟨c, ha, ht⟩

def VerifyingCall.initialization (c : VerifyingCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  pLength := c.input.components.pLength
  qLength := c.input.components.qLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem VerifyingShaped.initialization {reference : VerifyingCall} {s : State}
    (h : VerifyingShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .rdi = c.layout.base := hs.rdi
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  have hkey := c.pre.keySource.congrK hs.frame hs.keep
  have hps : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.components.p := source_take hkey
  have hqs : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.components.q := by
    change Src s c.input.base usedBytes (c.original.gpr .rdi + c.original.gpr .rdx) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega)
  rw [hag.layout] at hf hr hscr hps hqs
  rw [hag.pBytes] at hps
  rw [hag.qBytes] at hqs
  exact ⟨hscr, hr, hf, hps, hqs⟩

abbrev AcceptedVerifyingCall := {c : VerifyingCall // c.input.accepted = true}

theorem verifyingWorkspaces_ct : RelCT isa (Two (fun c : AcceptedVerifyingCall => VerifyingShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedVerifyingCall => VerifyingReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedVerifyingCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (verifyingInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def VerifyingCall.schedule (c : VerifyingCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
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

theorem VerifyingAgrees.prefixLength {reference c : VerifyingCall} (h : VerifyingAgrees reference c) :
    c.input.prefixLength = reference.input.prefixLength := by
  unfold VerifyingInput.prefixLength
  rw [h.digestLength, h.qBytes]

theorem VerifyingReady.body {reference : VerifyingCall} {s : State} (ha : reference.input.accepted = true)
    (h : VerifyingReady reference s) : ∃ pi qi, VerifyingBodyPre (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, _, hk⟩ := h
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  change Ready (c.layout.withInverses pi qi) s at hr
  change VerificationOperands (c.layout.withInverses pi qi) c.input.values c.input.components.q s at ho
  rw [hag.layout] at hr ho hmask
  refine ⟨pi, qi, hr, ⟨c.input.values, c.input.components.q, ho, ?_⟩,
    ⟨true, hmask⟩⟩
  change (c.input.digest.take _).length = reference.input.prefixLength
  rw [List.length_take, Nat.min_comm]
  exact hag.prefixLength

theorem verifyingReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedVerifyingCall => VerifyingReady c.val) s₁ s₂) : Two VerifyingBodyPre s₁ s₂ := by
  obtain ⟨reference, h₁, h₂⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1 h₂.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂⟩

theorem verifyingSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedVerifyingCall => VerifyingShaped c.val))
      (seqs [SignVerify.workspaces, Checks.publicKey Sq.mm M.mm,
        Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
        Core.verify Sq.mm M.mm, Checks.equal (Core.scalar u) Core.signatureR, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq verifyingWorkspaces_ct ?_
  apply RelCT.seqs_append (a := [Checks.publicKey Sq.mm M.mm,
    Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
    Core.verify Sq.mm M.mm, Checks.equal (Core.scalar u) Core.signatureR])
    (b := [.block SignVerify.result]) (by simp) (by simp)
  exact (verifyBody_ct M Sq).mono (fun _ _ h => verifyingReady_related h) (fun _ _ h => h)

end VG.Proof.Dsa.X86_64
