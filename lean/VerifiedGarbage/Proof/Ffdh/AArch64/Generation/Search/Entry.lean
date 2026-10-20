module
public import VerifiedGarbage.Impl.Ffdh.AArch64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Data
public import VerifiedGarbage.Proof.Ffdh.ControlMemory

import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # The parameter search's entry (AArch64)

The stack arguments are loaded, the caller's `x19` saved in word 4 and the
arguments stored in the controller's words; then, in the frame saving
`x30`, the controller is at the tape's start with its attempts
(`search_start`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue)
open VG.Impl.Ffdh.AArch64.Generation.Search

def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .x19), (5, s.gpr .x0), (6, s.gpr .x1), (7, s.gpr .x2), (8, s.gpr .x3),
    (9, BitVec.ofNat 64 (genGen s)), (10, s.gpr .x5), (11, s.gpr .x6), (12, 0), (13, s.gpr .x7),
    (15, stackArg s 0)]

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 16 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem input_args {p : SPub} {s : State} (h : SInput p s) (j : Nat) (hj : j < 2) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs s, ?_, ?_⟩
  · rw [h.1.2.2.1]
    exact List.mem_append_left _ (by simp [inReads])
  · simp only [inArgs, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- The stack arguments and the generator, before the stores. -/
abbrev entryRegs : List Reg := [.x4, .x8, .x9, .x13, .x14, .x19]

theorem entry_ok {p : SPub} {s : State} (h : SInput p s) :
    WP isa (.block entry) s fun t =>
      (t.gpr .x19 = p.control ∧ t.mem = writeController s.mem p.control (entryValues s)) ∧
      Keep entryRegs s t := by
  have scr := h.control_scr (t := s) rfl
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = p.control :=
    congrArg SPub.control h.2
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha0 : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using input_args h 0 (by decide)
  have ha1 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := input_args h 1 (by decide)
  refine WP.keep entryRegs ?_ (by decide) (by decide) (by decide +kernel)
  unfold entry writeController entryValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, exec_addSp (show 0 < 4096 by decide), imm64 (show 0 < 65536 by decide),
    VG.Proof.RsaKeyGen.AArch64.exec_addImm_w (show 0 < 4096 by decide), zext32, hd, ha0, ha1,
    hs 32 (by decide), hs 40 (by decide), hs 48 (by decide), hs 56 (by decide), hs 64 (by decide),
    hs 72 (by decide), hs 80 (by decide), hs 88 (by decide), hs 96 (by decide), hs 104 (by decide),
    hs 120 (by decide)]
  simp only [stackArg, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  rfl

/-- The state the body of the frame saving `x30` starts in (`WP.frameReg`). -/
abbrev pushedX30 (t : State) : State :=
  { t with sp := t.sp - 16, mem := t.mem.write (t.sp - 16) 8 (t.gpr .x30) }

private theorem word_zero (m : Mem) (B : Addr) : word m B 0 = m.readW B 64 := by
  simp only [Bignum.word, off, BitVec.add_zero]

theorem entry_headers {p : SPub} {s : State} (h : SInput p s) :
    Slots (writeController s.mem p.control (entryValues s)) p.control (p.headers 0 p.attempts) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hw1, hw2, -⟩ := h.1
  cases h.2
  intro e he
  simp only [SPub.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (entryValues_bound s) _ (by dsimp only; decide)] <;>
    simp only [sOfState, controllerValue, entryValues,
      List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.sub_zero, Nat.mul_zero, BitVec.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 8), word_zero]
  · simp only [Bignum.word, off, Nat.reduceMul]
    exact hw1.trans (by simp only [genLen, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  · simp only [Bignum.word, off, Nat.reduceMul]
    exact hw2
  all_goals rfl

/-- The push of `x30` writes only below the stack pointer. -/
theorem push_frame {p : SPub} {s : State} (h : SInput p s) (m : Mem) (v : BitVec 64) :
    Frame (SInput.callChanges s) m (m.write (s.sp - 16) 8 v) := by
  refine Frame.write (Frame.refl _ _) (r := below s.sp stackUse)
    (by simp [SInput.callChanges]) _ ?_
  have := h.1.2.1
  exact Offset.contains_below s.sp (a := 16) (b := 32) (by decide) (by decide) (by decide)

theorem search_start {p : SPub} {s t : State} (h : SInput p s)
    (hx : t.gpr .x19 = p.control) (hm : t.mem = writeController s.mem p.control (entryValues s))
    (k : Keep entryRegs s t) :
    SLive p s 0 p.attempts (pushedX30 t) := by
  have hf := writeController_frame s.mem p.control (entryValues s) (entryValues_bound s)
  have hf₁ : Frame (SInput.changes s) s.mem t.mem := by
    rw [hm]
    exact hf.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inCtl s, by simp [SInput.changes, inWrites], by rw [h.ctl_eq]; exact fun _ hi => hi⟩
  have hp := push_frame h t.mem (t.gpr .x30)
  rw [← k.sp] at hp
  have hf₂ : Frame (SInput.changes s) s.mem (pushedX30 t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 16) : word (pushedX30 t).mem p.control (8 * j) = word t.mem p.control (8 * j) :=
    h.control_frame hp j hj
  refine ⟨h, Nat.zero_le _, Nat.le_refl _, k.rd, k.wr, ?_, hx, ?_, k.vcs, ?_, ?_, ?_⟩
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
  · intro e he
    rw [hc e.1 (SPub.headers_index he), hm]
    exact entry_headers h e he

end VG.Proof.Ffdh.AArch64.Generation
