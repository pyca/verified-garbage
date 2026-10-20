module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyState
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateCalls
import VerifiedGarbage.Proof.Framework.Offset

/-! # Modulus preparation preserves key-generation input and call geometry -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyGeneratePrepare_next (prepare : Prog isa) (prep : KeyPrepareLaw prepare) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (size : rb.length = p.k) (h : KeyScalarInput p slots rb s) (calls : KeyCallMemory p s) :
    WP isa prepare s (fun t => KeyPrepared p slots rb t ∧ KeyCallMemory p t) := by
  refine WP.mono (prep.correct s h.context calls stable h0 h24 h32 large odd normalized) ?_
  rintro t ⟨context, ready, modulus, r2, frame, rest⟩
  have entropy := h.entropy.after_frame frame rest (by
    intro r hr
    simp only [keyPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact h.entropy.separate
    · rw [size]; exact h.entropyStack.sub_right (Offset.sub_base _ (by decide))
    · rw [size]; exact h.entropyStack.sub_right (Offset.sub_base _ (by decide))
    · rw [size]; exact calls.entropy)
  exact ⟨⟨⟨context, entropy, h.outputs.after rest, by rw [rest.sp]; exact h.entropyStack⟩, ready, modulus, r2⟩, calls.after rest⟩

end VG.Proof.Ffdh.Arm
