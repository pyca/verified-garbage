module

public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingPublic
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT

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
