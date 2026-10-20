module

import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPrepareLaw
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPrepare
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw

/-! Cached RSA prefix import within the existing FFDH local argument frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem cachedPrepareAt_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (environment : CachedGenerationContext p s)
    (stable : stableSlots slots = true) (h52 : 52 ∈ slots)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.CachedPrepare.code s fun t =>
      Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Frame (keyPrepareWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.CachedPrepare.code, WP.seq_iff]
  refine WP.mono (prepareArgs_ok s 24 h stable h24 h32 h0) ?_
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
  have environmentU := environment.after fullU (restU.mono (by simp [roundClobbers]))
  refine WP.mono (cachedPrepareBody_ok u input contextU environmentU h52 stable) ?_
  rintro t ⟨contextT, readyT, modulus, r2, frameT, restT⟩
  have frame : Frame (keyPrepareWrites p s) s.mem t.mem :=
    (frameU.mono (by
      intro r hr
      simp only [keyPrepareWrites, prepareAtWrites, List.mem_append, List.mem_cons]
      exact Or.inl (Or.inr hr))).trans
    (frameT.mono (by simp [keyPrepareWrites, prepareAtWrites]))
  exact ⟨contextT, readyT, modulus, r2, frame,
    (restU.mono (by simp [roundClobbers])).trans restT⟩

end VG.Proof.Ffdh.Arm
