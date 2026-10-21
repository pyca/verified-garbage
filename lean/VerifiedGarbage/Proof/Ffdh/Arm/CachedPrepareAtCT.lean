module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedPrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPrepareCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedPrepareState
import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPrepareLaw

/-! The public FFDH argument adapter preserves the canonical cached environment. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem cachedPrepareArgs_next (s : State) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (h : Context p slots s ∧ CachedGenerationContext p s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24)) s (CachedPrepareInitial p slots) := by
  refine WP.mono (prepareArgs_ok s 24 h.1 stable h24 h32 h0) ?_
  rintro u ⟨contextU, stack, _, countU, _, frameU, restU⟩
  have sourceU := contextU.pBytes
  have bytes : Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k = p.dom.take p.k := by
    simpa only [p.pLength] using sourceU.bytes
  have input : PrepareInput p.base p.domain p.len p.k u :=
    ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
      p.minLength, p.maxLength, p.publicSpace,
      by rw [← p.pLength]; exact sourceU.fits,
      by rw [← p.pLength]; exact sourceU.readable,
      by rw [← p.pLength]; exact sourceU.separate,
      by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
  have fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.sub (by
    intro r hr
    refine ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], ?_⟩
    simp only [prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide))
  exact ⟨input, contextU, h.2.after fullU (restU.mono (by simp [roundClobbers]))⟩

theorem cachedPrepareAt_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h52 : 52 ∈ slots)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => (Context p slots s ∧ CachedGenerationContext p s) ∧
      (Context p slots t ∧ CachedGenerationContext p t) ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.CachedPrepare.code (fun _ _ => True) := by
  have args := (prepareArgs_ct 24).mono
    (P' := fun (s t : State) => (Context p slots s ∧ CachedGenerationContext p s) ∧
      (Context p slots t ∧ CachedGenerationContext p t) ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  exact relCT_chain args (cachedPrepareArgs_next · stable h0 h24 h32 large odd)
    (cachedPrepareArgs_next · stable h0 h24 h32 large odd) (cachedPrepareBody_ct stable h52)

theorem cachedPrepareLaw : EnvironmentPrepareLaw cachedGenerationEnvironment
    VG.Impl.Ffdh.Arm.CachedPrepare.code where
  correct := by
    intro s p slots h environment _calls stable h52 h0 h24 h32 large odd _normalized
    exact cachedPrepareAt_ok s h environment stable h52 h0 h24 h32 large odd
  ct := by
    intro p slots stable h52 h0 h24 h32 large odd _normalized
    exact (cachedPrepareAt_ct stable h52 h0 h24 h32 large odd).mono
      (fun _ _ h => ⟨⟨h.1.1.1, h.1.2⟩, ⟨h.2.1.1.1, h.2.1.2⟩, h.2.2.2⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm
