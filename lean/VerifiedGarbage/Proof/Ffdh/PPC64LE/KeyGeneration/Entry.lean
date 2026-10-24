module
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Data
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Live

/-! # The key-generation controller's entry (PPC64LE)

The stack arguments are loaded, the caller's `r31` saved in word 4 and the
arguments stored in the controller's words; then, in the frame saving the
link register, the controller is at the tape's start (`key_start`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.Ffdh.PPC64LE.Generation (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue)
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search

def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .r31), (5, s.gpr .r3), (6, s.gpr .r5), (7, s.gpr .r8), (8, s.gpr .r9), (15, s.gpr .r7),
    (9, stackArg s 0), (10, stackArg s 1), (11, 0), (12, stackArg s 2), (13, stackArg s 3)]

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 16 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem input_args {p : KeyPublic} {s : State} (h : KeyInput p s) (j : Nat) (hj : j < 5) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs s, ?_, ?_⟩
  · rw [h.1.2.2.1]
    exact List.mem_append_left _ (by simp [inReads])
  · simp only [inArgs, stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem arg_value (s : State) (j : Nat) :
    s.mem.readW (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * j)) 64 = stackArg s j := by
  simp only [stackArg, stackArgAddr]
  rw [VG.Offset.add_add]
  congr 3
  omega

/-- The registers the entry writes. -/
abbrev entryRegs : List Reg := [.r0, .r4, .r6, .r10, .r11, .r12, .r31]

theorem entry_ok {p : KeyPublic} {s : State} (h : KeyInput p s) :
    WP isa (.block entry) s fun t =>
      (t.gpr .r31 = p.control ∧ t.mem = writeController s.mem p.control (entryValues s)) ∧
      Keep entryRegs s t := by
  have scr := h.control_scr (t := s) rfl
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hc : stackArg s 4 = p.control := congrArg KeyPublic.control h.2
  have v0 : s.mem.readW (s.sp + BitVec.ofNat 64 96) 64 = stackArg s 0 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using arg_value s 0
  have v1 := arg_value s 1
  have v2 := arg_value s 2
  have v3 := arg_value s 3
  have v4 : s.mem.readW (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 32) 64 = p.control :=
    (arg_value s 4).trans hc
  have a0 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 96) 8 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using input_args h 0 (by decide)
  have a1 := input_args h 1 (by decide)
  have a2 := input_args h 2 (by decide)
  have a3 := input_args h 3 (by decide)
  have a4 := input_args h 4 (by decide)
  simp only [Nat.reduceMul] at v1 v2 v3 a1 a2 a3 a4
  have w1 := v1; have w2 := v2; have w3 := v3; have w4 := v4
  have b1 := a1; have b2 := a2; have b3 := a3; have b4 := a4
  rw [VG.Offset.add_add] at w1 w2 w3 w4 b1 b2 b3 b4
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  refine WP.keep entryRegs ?_ (by decide)
  unfold entry writeController entryValues
  simp only [List.foldl_cons, List.foldl_nil]
  prun [ldf, stf, ea, v0, v1, v2, v3, v4, a0, a1, a2, a3, a4, w1, w2, w3, w4, b1, b2, b3, b4, hs 32 (by decide), hs 40 (by decide),
    hs 48 (by decide), hs 56 (by decide), hs 64 (by decide), hs 72 (by decide), hs 80 (by decide),
    hs 88 (by decide), hs 96 (by decide), hs 104 (by decide), hs 120 (by decide)]
  refine ⟨BitVec.add_zero _, ?_⟩
  rfl

private theorem word_zero (m : Mem) (B : Addr) : word m B 0 = m.readW B 64 := by
  simp only [Bignum.word, off, BitVec.add_zero]

theorem KeyInput.width_word {p : KeyPublic} {s : State} (h : KeyInput p s) :
    s.mem.readW (stackArg s 4 + 16) 64 = BitVec.ofNat 64 (keyLen s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hw⟩ := h.1
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
  all_goals first
    | rfl
    | (simp only [Bignum.word, off]; rfl)
    | (simp only [Bignum.word, off, Nat.reduceMul]
       exact hw.trans (by simp only [keyLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]))

/-- The push of the frame saving the link register writes only below the
stack pointer. -/
theorem push_frame (s : State) (m : Mem) (v : BitVec 64) :
    Frame (KeyInput.callChanges s) m ((m.write (s.sp - 48) 8 s.sp).write (s.sp - 48 + 32) 8 v) := by
  have e : s.sp - 48 + 32 = s.sp - BitVec.ofNat 64 16 := by bv_omega
  have hr : below s.sp stackUse ∈ KeyInput.callChanges s := by simp [KeyInput.callChanges]
  refine Frame.write (Frame.write (Frame.refl _ _) hr _ ?_) hr _ ?_
  · exact Offset.contains_below s.sp (a := 48) (b := 176) (by decide) (by decide) (by decide)
  · rw [e]; exact Offset.contains_below s.sp (a := 16) (b := 176) (by decide) (by decide) (by decide)

theorem key_start {p : KeyPublic} {s t : State} (h : KeyInput p s)
    (hx : t.gpr .r31 = p.control) (hm : t.mem = writeController s.mem p.control (entryValues s))
    (k : Keep entryRegs s t) :
    KeyLive p s 0 p.keys p.scalars (framed .r0 t) := by
  have hf := writeController_frame s.mem p.control (entryValues s) (entryValues_bound s)
  have hf₁ : Frame (KeyInput.changes s) s.mem t.mem := by
    rw [hm]
    exact hf.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inCtl s, by simp [KeyInput.changes, inWrites], by rw [← h.2]; exact fun _ hi => hi⟩
  have hp := push_frame s t.mem (t.gpr .r0)
  rw [← k.sp] at hp
  have hf₂ : Frame (KeyInput.changes s) s.mem (framed .r0 t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 16) : word (framed .r0 t).mem p.control (8 * j) = word t.mem p.control (8 * j) :=
    h.control_frame hp j hj
  refine ⟨h, Nat.zero_le _, h.keys_le, h.scalars_le, k.rd, k.wr, ?_, hx, ?_, ?_, ?_, ?_, ?_⟩
  · show t.sp - 48 = p.sp - 48
    rw [k.sp, h.sp_eq]
  · intro r hr h31
    exact k.gpr r (by revert r hr h31; decide)
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

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
