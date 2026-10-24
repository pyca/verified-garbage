module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Entry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Live
import VerifiedGarbage.Proof.Framework.Offset

/-! # After its entry, in the frame saving `x30`, the controller is at the tape's start -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue)

/-- The state the body of the frame saving `x30` starts in (`WP.frameReg`). -/
abbrev pushedX30 (t : State) : State :=
  { t with sp := t.sp - 16, mem := t.mem.write (t.sp - 16) 8 (t.gpr .x30) }

private theorem word_zero (m : Mem) (B : Addr) : word m B 0 = m.readW B 64 := by
  simp only [Bignum.word, off, BitVec.add_zero]

theorem KeyInput.width_word {p : KeyPublic} {s : State} (h : KeyInput p s) :
    s.mem.readW (stackArg s 4 + 16) 64 = BitVec.ofNat 64 (keyLen s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hw, -, -⟩ := h.1
  exact hw

theorem entry_headers {p : KeyPublic} {s : State} (h : KeyInput p s) :
    Slots (writeController s.mem p.control (entryValues s)) p.control
      (p.headers 0 p.keys p.scalars) := by
  have hw := h.width_word
  cases h.2
  intro e he
  simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (entryValues_bound s) _ (by dsimp only; decide)] <;>
    simp only [keyOfState, controllerValue, entryValues,
      List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.sub_zero, Nat.mul_zero, BitVec.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 8), word_zero]
  · simp only [Bignum.word, off]
    rfl
  · simp only [Bignum.word, off, Nat.reduceMul]
    exact hw.trans (by simp only [keyLen, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  all_goals rfl

/-- The push of `x30` writes only below the stack pointer. -/
theorem push_frame {p : KeyPublic} {s : State} (h : KeyInput p s) (m : Mem) (v : BitVec 64) :
    Frame (KeyInput.callChanges s) m (m.write (s.sp - 16) 8 v) := by
  refine Frame.write (Frame.refl _ _) (r := below s.sp stackUse)
    (by simp [KeyInput.callChanges]) _ ?_
  have := h.1.2.1
  exact Offset.contains_below s.sp (a := 16) (b := 64) (by decide) (by decide) (by decide)

theorem key_start {p : KeyPublic} {s t : State} (h : KeyInput p s)
    (hx : t.gpr .x19 = p.control) (hm : t.mem = writeController s.mem p.control (entryValues s))
    (k : Keep [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x19] s t) :
    KeyLive p s 0 p.keys p.scalars (pushedX30 t) := by
  have hf := writeController_frame s.mem p.control (entryValues s) (entryValues_bound s)
  have hf₁ : Frame (KeyInput.changes s) s.mem t.mem := by
    rw [hm]
    exact hf.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inCtl s, by simp [KeyInput.changes, inWrites], by rw [← h.2]; exact fun _ hi => hi⟩
  have hp := push_frame h t.mem (t.gpr .x30)
  rw [← k.sp] at hp
  have hf₂ : Frame (KeyInput.changes s) s.mem (pushedX30 t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 16) : word (pushedX30 t).mem p.control (8 * j) = word t.mem p.control (8 * j) :=
    h.control_frame hp j hj
  refine ⟨h, Nat.zero_le _, h.keys_le, h.scalars_le, k.rd, k.wr, ?_, hx, ?_, k.vcs, ?_, ?_, ?_, ?_,hf₂⟩
  · show t.sp - 16 = p.sp - 16
    rw [k.sp, h.sp_eq]
  · intro r hr h19 _
    exact k.gpr r (by revert r hr h19; decide)
  · rw [show (32 : Nat) = 8 * 4 from rfl, hc 4 (by decide), hm,
      writeController_word _ _ _ (entryValues_bound s) 4 (by decide)]
    rfl
  · rw [h.random_frame hf₂]
    cases h.2
    rfl
  · rw [h.domain_frame hf₂]
    cases h.2
    rfl
  · intro e he
    rw [hc e.1 (KeyPublic.headers_index he), hm]
    exact entry_headers h e he

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
