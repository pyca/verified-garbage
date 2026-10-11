import VerifiedGarbage.Proof.Seed.Arm.Lanes

/-!
# The steps of a round, lane by lane

As on AArch64 (`Proof/Seed/AArch64/Steps.lean`): each step of the round
(`step1` … `step4`) on one lane meets its `LaneSpec` (`LaneOk`); `lanes_ok`
then gives it on all eight. The halves `L` and `R` are at `l` and `r`, the
arrays of `L0`/`R0`, whose second words are 8 slots on.
-/

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Seed.Arm
open VG.Impl.Aes.Arm (sb t0 t1 u7 kp ldS stS eorR)

-- The steps share one set of rewrites, not all of which each step uses.
set_option linter.unusedSimpArgs false

/-- The two places of the halves. -/
def halves : List Nat := [arrSlot 0, arrSlot 2]

theorem mem_tA : tSlot 0 ∈ arrays := by decide
theorem mem_aA : aSlot ∈ arrays := by decide
theorem mem_cA : cSlot ∈ arrays := by decide
theorem mem_dA : dSlot ∈ arrays := by decide

theorem half_mem {h : Nat} (hh : h ∈ halves) : h ∈ arrays ∧ h + 8 ∈ arrays ∧
    h ≠ tSlot 0 ∧ h ≠ aSlot ∧ h ≠ cSlot ∧ h ≠ dSlot ∧ h + 8 ≠ tSlot 0 ∧ h + 8 ≠ aSlot ∧
    h + 8 ≠ cSlot ∧ h + 8 ≠ dSlot ∧ h ≠ h + 8 := by
  simp only [halves, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl <;> decide

theorem tSlot_lane (b : Nat) : tSlot b = tSlot 0 + b := by simp [tSlot]

theorem exec_eorR (s : State) (d n m : Reg) :
    exec (eorR d n m) s = some (s.setReg d (s.gpr n ^^^ s.gpr m)) := rfl

theorem exec_addR (s : State) (d n m : Reg) :
    exec (addR d n m) s = some (s.setReg d (s.gpr n + s.gpr m)) := rfl

theorem room_setReg {s : State} (h : Room s) {r : Reg} (hr : r ≠ sb) (v : BitVec 32) :
    Room (s.setReg r v) := h.congr (gpr_setReg_of_ne _ _ (Ne.symm hr)) rfl

theorem room_setMem {s : State} (h : Room s) (m : Mem) : Room (setMem s m) := h.congr rfl rfl

theorem lane_slot' {k b : Nat} (hk : k ∈ arrays) (hb : b < 8) : k + b < slots := lane_slot hk hb

/-- Reading a lane after a write to another. -/
theorem readW_writeW_lane {s : State} (h : Room s) {m : Mem} {k b k' b' : Nat} (hk : k ∈ arrays)
    (hb : b < 8) (hk' : k' ∈ arrays) (hb' : b' < 8) (hne : k ≠ k' ∨ b ≠ b') (v : BitVec 32) :
    (m.writeW (slotA s (k' + b')) v).readW (slotA s (k + b)) 32 = m.readW (slotA s (k + b)) 32 :=
  Mem.readW_writeW_sep (lane_sep h hk hb hk' hb' hne) (by decide)

theorem lv_eq (s : State) (k b : Nat) : s.mem.readW (slotA s (k + b)) 32 = lv s k b := rfl

def sp1 (r : Nat) (k0 k1 : BitVec 32) : LaneSpec :=
  [(aSlot, fun x => x r ^^^ k0), (tSlot 0, fun x => x r ^^^ k0 ^^^ x (r + 8) ^^^ k1)]

def sp2 : LaneSpec := [(cSlot, fun x => x (tSlot 0)), (tSlot 0, fun x => x (tSlot 0) + x aSlot)]

def sp3 : LaneSpec := [(dSlot, fun x => x (tSlot 0)), (tSlot 0, fun x => x (tSlot 0) + x cSlot)]

def sp4 (l : Nat) : LaneSpec :=
  [(l + 8, fun x => x (l + 8) ^^^ x (tSlot 0)), (l, fun x => (x (tSlot 0) + x dSlot) ^^^ x l)]

/-- The round key's halves are in `u7` and `lr`. -/
def KeysIn (k0 k1 : BitVec 32) (s : State) : Prop := Room s ∧ s.gpr .r12 = k0 ∧ s.gpr .lr = k1

theorem gpr_t0_sb : ∀ r ∈ [t0, t1], r ≠ sb := by decide

theorem step1_ok {r : Nat} (hr : r ∈ halves) (k0 k1 : BitVec 32) {b : Nat} (hb : b < 8) (s : State)
    (h : KeysIn k0 k1 s) :
    ∃ s', runBlock isa (step1 r b) s = some s' ∧ LaneOk s s' (sp1 r k0 k1) b := by
  obtain ⟨h, hk0, hk1⟩ := h
  obtain ⟨hR, hR8, -, hRa, -, -, -, hR8a, -, -, -⟩ := half_mem hr
  rw [step1, tSlot_lane, runBlock_cons, exec_ldS h (lane_slot hR hb), runStep_some, runBlock_cons,
    exec_eorR, runStep_some, runBlock_cons,
    exec_stS (room_setReg (room_setReg h (by decide) _) (by decide) _) (lane_slot mem_aA hb), runStep_some,
    runBlock_cons, exec_ldS (room_setMem (room_setReg (room_setReg h (by decide) _) (by decide) _) _)
      (lane_slot hR8 hb), runStep_some,
    runBlock_cons, exec_eorR, runStep_some, runBlock_cons, exec_eorR, runStep_some, runBlock_cons,
    exec_stS (room_setReg (room_setReg (room_setReg (room_setMem (room_setReg (room_setReg h (by decide) _)
      (by decide) _) _) (by decide) _) (by decide) _) (by decide) _) (lane_slot mem_tA hb), runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp (disch := decide) only [laneWrites, sp1, List.foldl_cons, List.foldl_nil, gpr_setReg, reduceCtorEq,
      ↓reduceIte, gpr_setMem, mem_setMem, mem_setReg, slotA_setReg, slotA_setMem, slotW_setMem, slotW_setReg,
      t0, t1, u7, hk0, hk1]
    rw [readW_writeW_lane h hR8 hb mem_aA hb (Or.inl hR8a)]
    rfl
  · simp only [gpr_setReg, gpr_setMem, h1, h2, ↓reduceIte]

theorem step2_ok {b : Nat} (hb : b < 8) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step2 b) s = some s' ∧ LaneOk s s' sp2 b := by
  rw [step2, tSlot_lane, runBlock_cons, exec_ldS h (lane_slot mem_tA hb), runStep_some, runBlock_cons,
    exec_stS (room_setReg h (by decide) _) (lane_slot mem_cA hb), runStep_some, runBlock_cons,
    exec_ldS (room_setMem (room_setReg h (by decide) _) _) (lane_slot mem_aA hb), runStep_some,
    runBlock_cons, exec_addR, runStep_some, runBlock_cons,
    exec_stS (room_setReg (room_setReg (room_setMem (room_setReg h (by decide) _) _) (by decide) _)
      (by decide) _) (lane_slot mem_tA hb), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp (disch := decide) only [laneWrites, sp2, List.foldl_cons, List.foldl_nil, gpr_setReg, reduceCtorEq,
      ↓reduceIte, gpr_setMem, mem_setMem, mem_setReg, slotA_setReg, slotA_setMem, slotW_setMem, slotW_setReg,
      t0, t1]
    rw [readW_writeW_lane h mem_aA hb mem_cA hb (Or.inl (by decide))]
    rfl
  · simp only [gpr_setReg, gpr_setMem, h1, h2, ↓reduceIte]

theorem step3_ok {b : Nat} (hb : b < 8) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step3 b) s = some s' ∧ LaneOk s s' sp3 b := by
  rw [step3, tSlot_lane, runBlock_cons, exec_ldS h (lane_slot mem_tA hb), runStep_some, runBlock_cons,
    exec_stS (room_setReg h (by decide) _) (lane_slot mem_dA hb), runStep_some, runBlock_cons,
    exec_ldS (room_setMem (room_setReg h (by decide) _) _) (lane_slot mem_cA hb), runStep_some,
    runBlock_cons, exec_addR, runStep_some, runBlock_cons,
    exec_stS (room_setReg (room_setReg (room_setMem (room_setReg h (by decide) _) _) (by decide) _)
      (by decide) _) (lane_slot mem_tA hb), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp (disch := decide) only [laneWrites, sp3, List.foldl_cons, List.foldl_nil, gpr_setReg, reduceCtorEq,
      ↓reduceIte, gpr_setMem, mem_setMem, mem_setReg, slotA_setReg, slotA_setMem, slotW_setMem, slotW_setReg,
      t0, t1]
    rw [readW_writeW_lane h mem_cA hb mem_dA hb (Or.inl (by decide))]
    rfl
  · simp only [gpr_setReg, gpr_setMem, h1, h2, ↓reduceIte]

theorem step4_ok {l : Nat} (hl : l ∈ halves) {b : Nat} (hb : b < 8) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step4 l b) s = some s' ∧ LaneOk s s' (sp4 l) b := by
  obtain ⟨hL, hL8, hLt, -, -, hLd, -, -, -, hL8d, hLL⟩ := half_mem hl
  rw [step4, tSlot_lane, runBlock_cons, exec_ldS h (lane_slot mem_tA hb), runStep_some, runBlock_cons,
    exec_ldS (room_setReg h (by decide) _) (lane_slot hL8 hb), runStep_some, runBlock_cons,
    exec_eorR, runStep_some, runBlock_cons,
    exec_stS (room_setReg (room_setReg (room_setReg h (by decide) _) (by decide) _) (by decide) _)
      (lane_slot hL8 hb), runStep_some, runBlock_cons,
    exec_ldS (room_setMem (room_setReg (room_setReg (room_setReg h (by decide) _) (by decide) _)
      (by decide) _) _) (lane_slot mem_dA hb), runStep_some, runBlock_cons, exec_addR, runStep_some,
    runBlock_cons,
    exec_ldS (room_setReg (room_setReg (room_setMem (room_setReg (room_setReg (room_setReg h (by decide) _)
      (by decide) _) (by decide) _) _) (by decide) _) (by decide) _) (lane_slot hL hb), runStep_some,
    runBlock_cons, exec_eorR, runStep_some, runBlock_cons,
    exec_stS (room_setReg (room_setReg (room_setReg (room_setReg (room_setMem (room_setReg (room_setReg
      (room_setReg h (by decide) _) (by decide) _) (by decide) _) _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _) (lane_slot hL hb), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp (disch := decide) only [laneWrites, sp4, List.foldl_cons, List.foldl_nil, gpr_setReg, reduceCtorEq,
      ↓reduceIte, gpr_setMem, mem_setMem, mem_setReg, slotA_setReg, slotA_setMem, slotW_setMem, slotW_setReg,
      t0, t1]
    rw [readW_writeW_lane h mem_dA hb hL8 hb (Or.inl (Ne.symm hL8d)),
      readW_writeW_lane h hL hb hL8 hb (Or.inl hLL)]
    rfl
  · simp only [gpr_setReg, gpr_setMem, h1, h2, ↓reduceIte]

end VG.Proof.Seed.Arm
