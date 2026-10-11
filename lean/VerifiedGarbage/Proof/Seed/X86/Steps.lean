import VerifiedGarbage.Proof.Seed.X86.Lanes

/-!
# The steps of a round, lane by lane

As on ARMv7 (`Proof/Seed/Arm/Steps.lean`): each step of the round
(`step1` … `step4`) on one lane meets its `LaneSpec` (`LaneOk`); `lanes_ok`
then gives it on all eight. The halves `L` and `R` are at `l` and `r`, the
arrays of `L0`/`R0`, whose second words are 8 slots on.
-/

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Seed.X86
open VG.Impl.Aes.X86 (sb slotAt movS st xorR xorS)

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

theorem room_setReg {s : State} (h : Room s) {r : Reg} (hr : r ≠ sb) (v : BitVec 32) :
    Room (s.setReg r v) := h.congr (gpr_setReg_of_ne _ _ (Ne.symm hr)) rfl

theorem room_arith {s : State} (h : Room s) (v : BitVec 32) (c o : Bool) : Room (arithFlags s v c o) :=
  h.congr rfl rfl

theorem room_setMem {s : State} (h : Room s) (m : Mem) : Room (setMem s m) := h.congr rfl rfl

theorem slotA_arith (s : State) (v : BitVec 32) (c o : Bool) (k : Nat) :
    slotA (arithFlags s v c o) k = slotA s k := rfl

theorem slotW_arith (s : State) (v : BitVec 32) (c o : Bool) (k : Nat) :
    slotW (arithFlags s v c o) k = slotW s k := rfl

/-- Reading a lane after a write to another. -/
theorem readW_writeW_lane {s : State} (h : Room s) {m : Mem} {k b k' b' : Nat} (hk : k ∈ arrays)
    (hb : b < 8) (hk' : k' ∈ arrays) (hb' : b' < 8) (hne : k ≠ k' ∨ b ≠ b') (v : BitVec 32) :
    (m.writeW (slotA s (k' + b')) v).readW (slotA s (k + b)) 32 = m.readW (slotA s (k + b)) 32 :=
  Mem.readW_writeW_sep (lane_sep h hk hb hk' hb' hne) (by decide)

def sp1 (r : Nat) (k0 k1 : BitVec 32) : LaneSpec :=
  [(aSlot, fun x => x r ^^^ k0), (tSlot 0, fun x => x r ^^^ k0 ^^^ x (r + 8) ^^^ k1)]

def sp2 : LaneSpec := [(cSlot, fun x => x (tSlot 0)), (tSlot 0, fun x => x (tSlot 0) + x aSlot)]

def sp3 : LaneSpec := [(dSlot, fun x => x (tSlot 0)), (tSlot 0, fun x => x (tSlot 0) + x cSlot)]

def sp4 (l : Nat) : LaneSpec :=
  [(l + 8, fun x => x (l + 8) ^^^ x (tSlot 0)), (l, fun x => (x (tSlot 0) + x dSlot) ^^^ x l)]

/-- The round key's halves are in `ecx` and `edx`. -/
def KeysIn (k0 k1 : BitVec 32) (s : State) : Prop := Room s ∧ s.gpr .ecx = k0 ∧ s.gpr .edx = k1

theorem step1_ok {r : Nat} (hr : r ∈ halves) (k0 k1 : BitVec 32) {b : Nat} (hb : b < 8) (s : State)
    (h : KeysIn k0 k1 s) :
    ∃ s', runBlock isa (step1 r b) s = some s' ∧ LaneOk s s' (sp1 r k0 k1) b := by
  obtain ⟨h, hk0, hk1⟩ := h
  obtain ⟨hR, hR8, -, hRa, -, -, -, hR8a, -, -, -⟩ := half_mem hr
  rw [step1, tSlot_lane, runBlock_cons, exec_movS h (lane_slot hR hb), runStep_some, runBlock_cons,
    exec_xorR, runStep_some, runBlock_cons,
    exec_st (room_setReg (room_arith (room_setReg h (by decide) _) _ _ _) (by decide) _) (lane_slot mem_aA hb),
    runStep_some, runBlock_cons,
    exec_xorS (room_setMem (room_setReg (room_arith (room_setReg h (by decide) _) _ _ _) (by decide) _) _)
      (lane_slot hR8 hb), runStep_some,
    runBlock_cons, exec_xorR, runStep_some, runBlock_cons,
    exec_st (room_setReg (room_arith (room_setReg (room_arith (room_setMem (room_setReg (room_arith
      (room_setReg h (by decide) _) _ _ _) (by decide) _) _) _ _ _) (by decide) _) _ _ _) (by decide) _)
      (lane_slot mem_tA hb), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp (disch := decide) only [laneWrites, sp1, List.foldl_cons, List.foldl_nil, gpr_setReg, reduceCtorEq,
      ↓reduceIte, gpr_setMem, mem_setMem, mem_setReg, mem_arithFlags, gpr_arithFlags, slotA_setReg, slotA_setMem,
      slotA_arith, slotW_arith, slotW_setMem, slotW_setReg, hk0, hk1]
    rw [readW_writeW_lane h hR8 hb mem_aA hb (Or.inl hR8a)]
    rfl
  · simp only [gpr_setReg, gpr_setMem, gpr_arithFlags, h1, h2, ↓reduceIte]

theorem step2_ok {b : Nat} (hb : b < 8) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step2 b) s = some s' ∧ LaneOk s s' sp2 b := by
  rw [step2, tSlot_lane, runBlock_cons, exec_movS h (lane_slot mem_tA hb), runStep_some, runBlock_cons,
    exec_st (room_setReg h (by decide) _) (lane_slot mem_cA hb), runStep_some, runBlock_cons,
    exec_addS (room_setMem (room_setReg h (by decide) _) _) (lane_slot mem_aA hb), runStep_some,
    runBlock_cons,
    exec_st (room_setReg (room_arith (room_setMem (room_setReg h (by decide) _) _) _ _ _) (by decide) _)
      (lane_slot mem_tA hb), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp (disch := decide) only [laneWrites, sp2, List.foldl_cons, List.foldl_nil, gpr_setReg, reduceCtorEq,
      ↓reduceIte, gpr_setMem, mem_setMem, mem_setReg, mem_arithFlags, gpr_arithFlags, slotA_setReg, slotA_setMem,
      slotA_arith, slotW_arith, slotW_setMem, slotW_setReg]
    rw [readW_writeW_lane h mem_aA hb mem_cA hb (Or.inl (by decide))]
    rfl
  · simp only [gpr_setReg, gpr_setMem, gpr_arithFlags, h1, h2, ↓reduceIte]

theorem step3_ok {b : Nat} (hb : b < 8) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step3 b) s = some s' ∧ LaneOk s s' sp3 b := by
  rw [step3, tSlot_lane, runBlock_cons, exec_movS h (lane_slot mem_tA hb), runStep_some, runBlock_cons,
    exec_st (room_setReg h (by decide) _) (lane_slot mem_dA hb), runStep_some, runBlock_cons,
    exec_addS (room_setMem (room_setReg h (by decide) _) _) (lane_slot mem_cA hb), runStep_some,
    runBlock_cons,
    exec_st (room_setReg (room_arith (room_setMem (room_setReg h (by decide) _) _) _ _ _) (by decide) _)
      (lane_slot mem_tA hb), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp (disch := decide) only [laneWrites, sp3, List.foldl_cons, List.foldl_nil, gpr_setReg, reduceCtorEq,
      ↓reduceIte, gpr_setMem, mem_setMem, mem_setReg, mem_arithFlags, gpr_arithFlags, slotA_setReg, slotA_setMem,
      slotA_arith, slotW_arith, slotW_setMem, slotW_setReg]
    rw [readW_writeW_lane h mem_cA hb mem_dA hb (Or.inl (by decide))]
    rfl
  · simp only [gpr_setReg, gpr_setMem, gpr_arithFlags, h1, h2, ↓reduceIte]

theorem step4_ok {l : Nat} (hl : l ∈ halves) {b : Nat} (hb : b < 8) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step4 l b) s = some s' ∧ LaneOk s s' (sp4 l) b := by
  obtain ⟨hL, hL8, hLt, -, -, hLd, -, -, -, hL8d, hLL⟩ := half_mem hl
  rw [step4, tSlot_lane, runBlock_cons, exec_movS h (lane_slot mem_tA hb), runStep_some, runBlock_cons,
    exec_movS (room_setReg h (by decide) _) (lane_slot hL8 hb), runStep_some, runBlock_cons,
    exec_xorR, runStep_some, runBlock_cons,
    exec_st (room_setReg (room_arith (room_setReg (room_setReg h (by decide) _) (by decide) _) _ _ _) (by decide) _)
      (lane_slot hL8 hb), runStep_some, runBlock_cons,
    exec_addS (room_setMem (room_setReg (room_arith (room_setReg (room_setReg h (by decide) _) (by decide) _) _ _ _)
      (by decide) _) _) (lane_slot mem_dA hb), runStep_some, runBlock_cons,
    exec_xorS (room_setReg (room_arith (room_setMem (room_setReg (room_arith (room_setReg (room_setReg h
      (by decide) _) (by decide) _) _ _ _) (by decide) _) _) _ _ _) (by decide) _) (lane_slot hL hb), runStep_some,
    runBlock_cons,
    exec_st (room_setReg (room_arith (room_setReg (room_arith (room_setMem (room_setReg (room_arith (room_setReg
      (room_setReg h (by decide) _) (by decide) _) _ _ _) (by decide) _) _) _ _ _) (by decide) _) _ _ _) (by decide) _)
      (lane_slot hL hb), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp (disch := decide) only [laneWrites, sp4, List.foldl_cons, List.foldl_nil, gpr_setReg, reduceCtorEq,
      ↓reduceIte, gpr_setMem, mem_setMem, mem_setReg, mem_arithFlags, gpr_arithFlags, slotA_setReg, slotA_setMem,
      slotA_arith, slotW_arith, slotW_setMem, slotW_setReg]
    rw [readW_writeW_lane h mem_dA hb hL8 hb (Or.inl (Ne.symm hL8d)),
      readW_writeW_lane h hL hb hL8 hb (Or.inl hLL)]
    rfl
  · simp only [gpr_setReg, gpr_setMem, gpr_arithFlags, h1, h2, ↓reduceIte]

end VG.Proof.Seed.X86
