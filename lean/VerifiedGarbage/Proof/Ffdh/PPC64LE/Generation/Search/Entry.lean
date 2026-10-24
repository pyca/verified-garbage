module
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Data
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The parameter search's entry (PPC64LE)

The stack arguments are loaded, the caller's `r31` saved in word 4 and the
arguments stored in the controller's words; then, in the frame saving the
link register, the controller is at the tape's start with its attempts
(`search_start`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue)
open VG.Impl.Ffdh.PPC64LE.Generation.Search

def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .r31), (5, s.gpr .r3), (6, s.gpr .r4), (7, s.gpr .r5), (8, s.gpr .r6),
    (9, BitVec.ofNat 64 (genGen s)), (10, s.gpr .r8), (11, s.gpr .r9), (12, 0), (13, s.gpr .r10),
    (15, stackArg s 0)]

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 16 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem input_args {p : SPub} {s : State} (h : SInput p s) (j : Nat) (hj : j < 2) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs s, ?_, ?_⟩
  · rw [h.1.2.2.1]
    exact List.mem_append_left _ (by simp [inReads])
  · simp only [inArgs, stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- The registers the entry writes. -/
abbrev entryRegs : List Reg := [.r0, .r7, .r11, .r12, .r31]

theorem gen_zext (x : BitVec 64) : (x.setWidth 32).setWidth 64 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq; simp

theorem entry_ok {p : SPub} {s : State} (h : SInput p s) :
    WP isa (.block entry) s fun t =>
      (t.gpr .r31 = p.control ∧ t.mem = writeController s.mem p.control (entryValues s)) ∧
      Keep entryRegs s t := by
  have scr := h.control_scr (t := s) rfl
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 64 = p.control := by
    rw [← congrArg SPub.control h.2]
    simp only [sOfState, stackArg, stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
    rw [VG.Offset.add_add]
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha0 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 96) 8 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using input_args h 0 (by decide)
  have ha1 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 8 :=
    input_args h 1 (by decide)
  have e104 : s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 = s.sp + BitVec.ofNat 64 104 := VG.Offset.add_add _ _ _
  have hd' : s.mem.readW (s.sp + BitVec.ofNat 64 104) 64 = p.control := by rw [← e104]; exact hd
  have ha1' : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 104) 8 := by rw [← e104]; exact ha1
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  refine WP.keep entryRegs ?_ (by decide)
  unfold entry writeController entryValues
  simp only [List.foldl_cons, List.foldl_nil]
  prun [ldf, stf, ea, hd, ha0, ha1, hd', ha1', hs 32 (by decide), hs 40 (by decide), hs 48 (by decide),
    hs 56 (by decide), hs 64 (by decide), hs 72 (by decide), hs 80 (by decide), hs 88 (by decide),
    hs 96 (by decide), hs 104 (by decide), hs 120 (by decide), BitVec.ushiftRight_zero]
  refine ⟨BitVec.add_zero _, ?_⟩
  rw [gen_zext]
  rfl

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

/-- The push of the frame saving the link register writes only below the
stack pointer. -/
theorem push_frame (s : State) (m : Mem) (v : BitVec 64) :
    Frame (SInput.callChanges s) m ((m.write (s.sp - 48) 8 s.sp).write (s.sp - 48 + 32) 8 v) := by
  have e : s.sp - 48 + 32 = s.sp - BitVec.ofNat 64 16 := by bv_omega
  have hr : below s.sp stackUse ∈ SInput.callChanges s := by simp [SInput.callChanges]
  refine Frame.write (Frame.write (Frame.refl _ _) hr _ ?_) hr _ ?_
  · exact Offset.contains_below s.sp (a := 48) (b := 336) (by decide) (by decide) (by decide)
  · rw [e]; exact Offset.contains_below s.sp (a := 16) (b := 336) (by decide) (by decide) (by decide)

theorem search_start {p : SPub} {s t : State} (h : SInput p s)
    (hx : t.gpr .r31 = p.control) (hm : t.mem = writeController s.mem p.control (entryValues s))
    (k : Keep entryRegs s t) :
    SLive p s 0 p.attempts (framed .r0 t) := by
  have hf := writeController_frame s.mem p.control (entryValues s) (entryValues_bound s)
  have hf₁ : Frame (SInput.changes s) s.mem t.mem := by
    rw [hm]
    exact hf.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inCtl s, by simp [SInput.changes, inWrites], by rw [h.ctl_eq]; exact fun _ hi => hi⟩
  have hp := push_frame s t.mem (t.gpr .r0)
  rw [← k.sp] at hp
  have hf₂ : Frame (SInput.changes s) s.mem (framed .r0 t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 16) : word (framed .r0 t).mem p.control (8 * j) = word t.mem p.control (8 * j) :=
    h.control_frame hp j hj
  refine ⟨h, Nat.zero_le _, Nat.le_refl _, k.rd, k.wr, ?_, hx, ?_, ?_, ?_, ?_⟩
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
  · intro e he
    rw [hc e.1 (SPub.headers_index he), hm]
    exact entry_headers h e he

end VG.Proof.Ffdh.PPC64LE.Generation
