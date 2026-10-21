module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Sm4.Arm.BatchFill
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Aes.Arm.Sbox
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem

/-! # Saving and restoring ARMv7 SM4-CTR's mode registers -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.BatchEntry

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm.BatchFill
open VG.Impl.Aes.Arm (sb movR)

/-- The outer saves are separate from the cipher's 1456-byte workspace
and the running counter at byte 1492. -/
theorem mode_slots : Spill.Slots 1456 1492 BatchCtr.modeSaved := by decide

theorem mode_restorable : Spill.Restorable .r12 BatchCtr.modeSaved := by decide

theorem mode_preserved : BatchCtr.modeSaved.map Prod.fst = preserved := by decide

def moves (s : State) : State :=
  ((((s.setReg sb (s.gpr .r12)).setReg .r4 (s.gpr .r0)).setReg .r5 (s.gpr .r1)).setReg .r6 (s.gpr .r2)).setReg .r7 (s.gpr .r3)

theorem moves_run (s : State) :
    runBlock isa [movR sb .r12, movR .r4 .r0, movR .r5 .r1, movR .r6 .r2, movR .r7 .r3] s = some (moves s) := by rfl

structure EntryPost (s : State) (B : BitVec 32) (s' : State) : Prop where
  base : s'.gpr sb = B
  key : s'.gpr .r4 = s.gpr .r0
  iv : s'.gpr .r5 = s.gpr .r1
  data : s'.gpr .r6 = s.gpr .r2
  left : s'.gpr .r7 = s.gpr .r3
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : Spill.Saved s'.mem (State.addr B) s.gpr BatchCtr.modeSaved
  frame : Frame [⟨State.addr B + BitVec.ofNat 64 1456, 36⟩] s.mem s'.mem

theorem entry_eq : BatchCtr.entry = ([.ldrSp .r12 0] : List Instr) ++ BatchCtr.save ++
    ([movR sb .r12, movR .r4 .r0, movR .r5 .r1, movR .r6 .r2, movR .r7 .r3] : List Instr) := rfl

theorem entry_wp {s : State} {B : BitVec 32}
    (ha : State.addr (s.sp + BitVec.ofNat 32 0) = stackArgAddr s 0)
    (hin : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4) (hb : stackArg s 0 = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr) :
    WP isa (.block BatchCtr.entry) s (EntryPost s B) := by
  rw [entry_eq, List.append_assoc]
  refine Proof.MdStream.Arm.wp_ldrSp (by decide) ha hin fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .r12 = B := u₁.gpr.trans hb
  have ws₁ : ∀ d, 1456 ≤ d → d + 4 ≤ 1492 →
      InRegions s₁.wr (State.addr (s₁.gpr .r12) + BitVec.ofNat 64 d) 4 := by
    intro d hd hd'
    rw [u₁.wr, b₁]
    exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by rw [total_eq]; omega) (by omega)⟩
  have saveWp := Spill.save_block_ok (b := .r12) mode_slots (s := s₁)
    (by rw [b₁]; rw [total_eq] at fitB; omega) ws₁
  obtain ⟨t₂, s₂, he₂, g₂, rd₂, wr₂, m₂⟩ := saveWp
  have sp₂ := VG.Arm.Exec.sp he₂
  have saved₂ : Spill.Saved s₂.mem (State.addr B) s.gpr BatchCtr.modeSaved := by
    intro p hp
    rw [m₂, b₁]
    have h := Spill.saveMem_saved (lo := 1456) (hi := 1492) (State.addr B) s₁.gpr s₁.mem BatchCtr.modeSaved mode_slots p hp
    rw [u₁.other _ (mode_restorable.ne hp)] at h
    exact h
  have frame₂ : Frame [⟨State.addr B + BitVec.ofNat 64 1456, 36⟩] s.mem s₂.mem := by
    rw [m₂, b₁, u₁.mem]
    exact Spill.saveMem_frame_slots mode_slots _ _ _
  refine (WP.block_append_iff (M := isa) (l₁ := BatchCtr.save) (l₂ := [movR sb .r12, movR .r4 .r0, movR .r5 .r1, movR .r6 .r2, movR .r7 .r3])).mpr ⟨t₂, s₂, he₂, WP.of_runBlock ⟨moves s₂, moves_run s₂, ?_⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, rd₂.trans u₁.rd, wr₂.trans u₁.wr, sp₂.trans u₁.sp, saved₂, frame₂⟩
  · simp only [moves, RegUpd.gpr_setReg, sb, reduceCtorEq, ↓reduceIte]
    rw [g₂, b₁]
  · simp only [moves, RegUpd.gpr_setReg, sb, reduceCtorEq, ↓reduceIte]
    rw [g₂, u₁.other _ (by decide)]
  · simp only [moves, RegUpd.gpr_setReg, sb, reduceCtorEq, ↓reduceIte]
    rw [g₂, u₁.other _ (by decide)]
  · simp only [moves, RegUpd.gpr_setReg, sb, reduceCtorEq, ↓reduceIte]
    rw [g₂, u₁.other _ (by decide)]
  · simp only [moves, RegUpd.gpr_setReg, sb, ↓reduceIte]
    rw [g₂, u₁.other _ (by decide)]

def restoreArgs (s : State) : State := s.setReg .r12 (s.gpr sb)

theorem restoreArgs_run (s : State) : runBlock isa [movR .r12 sb] s = some (restoreArgs s) := by rfl

theorem restore_wp {s : State} {B : BitVec 32} {g : Reg → BitVec 32} (hB : s.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (hsv : Spill.Saved s.mem (State.addr B) g BatchCtr.modeSaved) :
    WP isa (.block (([movR .r12 sb] : List Instr) ++ BatchCtr.restore)) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = g r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have b₁ : (restoreArgs s).gpr .r12 = B := (RegUpd.gpr_setReg_self _ _ _).trans hB
  have hs : Spill.Saved (restoreArgs s).mem (State.addr ((restoreArgs s).gpr .r12)) g BatchCtr.modeSaved := by
    rw [b₁]; exact hsv
  refine (WP.block_append_iff (M := isa) (l₁ := [movR .r12 sb]) (l₂ := BatchCtr.restore)).mpr (WP.of_runBlock ⟨restoreArgs s, restoreArgs_run s, ?_⟩)
  refine WP.mono (Spill.restore_block_ok (b := .r12) mode_slots mode_restorable (s := restoreArgs s)
    (by rw [b₁]; rw [total_eq] at fitB; omega)
    (fun d hd hd' => by
      rw [b₁]
      exact Covers.right hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by rw [total_eq]; omega) (by omega)⟩)
    hs) fun s' ⟨hreg, _, hm, hrd, hwr, hsp⟩ => ?_
  refine ⟨Spill.restored_of hreg (fun r hr => ?_), hm, hrd, hwr, hsp⟩
  rw [mode_preserved]; exact hr

end VG.Proof.Sm4.Arm.BatchEntry
