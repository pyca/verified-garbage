import VerifiedGarbage.Proof.Seed.AArch64.Lanes

/-!
# The steps of a round, lane by lane

As on x86-64: each step of the round (`step1` … `step4`) on one lane meets
its `LaneSpec` (`LaneOk`); `lanes_ok` then gives it on all sixteen.
-/

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Seed.AArch64

-- The steps share one set of rewrites, not all of which each step uses.
set_option linter.unusedSimpArgs false

theorem setWidth_setWidth_32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem mem_tA : tSlot 0 ∈ arrays := by decide
theorem mem_aA : aSlot ∈ arrays := by decide
theorem mem_cA : cSlot ∈ arrays := by decide
theorem mem_dA : dSlot ∈ arrays := by decide
theorem mem_L0 : arrSlot 0 ∈ arrays := by decide
theorem mem_L1 : arrSlot 1 ∈ arrays := by decide
theorem mem_R0 : arrSlot 2 ∈ arrays := by decide
theorem mem_R1 : arrSlot 3 ∈ arrays := by decide

theorem room_congr {s s' : State} (h : Room s) (hr : s'.gpr .x5 = s.gpr .x5) (hw : s'.wr = s.wr) :
    Room s' := by
  unfold Room scratchR at *; rw [hr, hw]; exact h

/-- Reading a lane after a write to another. -/
theorem readW_writeW_lane {m : Mem} {s : State} {k b k' b' : Nat} (hk : k ∈ arrays) (hb : b < 16)
    (hk' : k' ∈ arrays) (hb' : b' < 16) (h : k ≠ k' ∨ b ≠ b') (v : BitVec 32) :
    (m.writeW (laneA s k' b') v).readW (laneA s k b) 32 = m.readW (laneA s k b) 32 :=
  Mem.readW_writeW_sep (lane_sep hk hb hk' hb' h s) (by decide)

theorem lv_eq (s : State) (k b : Nat) : s.mem.readW (laneA s k b) 32 = lv s k b := rfl

def sp1 (k0 k1 : BitVec 32) : LaneSpec :=
  [(aSlot, fun x => x (arrSlot 2) ^^^ k0),
   (tSlot 0, fun x => x (arrSlot 2) ^^^ k0 ^^^ x (arrSlot 3) ^^^ k1)]

def sp2 : LaneSpec := [(cSlot, fun x => x (tSlot 0)), (tSlot 0, fun x => x (tSlot 0) + x aSlot)]

def sp3 : LaneSpec := [(dSlot, fun x => x (tSlot 0)), (tSlot 0, fun x => x (tSlot 0) + x cSlot)]

def sp4 : LaneSpec :=
  [(arrSlot 1, fun x => x (arrSlot 1) ^^^ x (tSlot 0)),
   (arrSlot 0, fun x => (x (tSlot 0) + x dSlot) ^^^ x (arrSlot 0))]

/-- The round key's halves are in `x16` and `x17`. -/
def KeysIn (k0 k1 : BitVec 32) (s : State) : Prop :=
  Room s ∧ (s.gpr .x16).setWidth 32 = k0 ∧ (s.gpr .x17).setWidth 32 = k1

theorem step1_ok (k0 k1 : BitVec 32) {b : Nat} (hb : b < 16) (s : State) (h : KeysIn k0 k1 s) :
    ∃ s', runBlock isa (step1 b) s = some s' ∧ LaneOk s s' (sp1 k0 k1) b := by
  obtain ⟨h, hk0, hk1⟩ := h
  rw [step1, runBlock_cons, exec_ldW_lane h mem_R0 hb, runStep_some, runBlock_cons,
    exec_eorW, runStep_some, runBlock_cons, exec_stW_lane ?h1 mem_aA hb, runStep_some,
    runBlock_cons, exec_ldW_lane ?h2 mem_R1 hb, runStep_some, runBlock_cons, exec_eorW, runStep_some,
    runBlock_cons, exec_eorW, runStep_some, runBlock_cons, exec_stW_lane ?h3 mem_tA hb, runStep_some,
    runBlock_nil]
  case h1 | h2 | h3 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [laneWrites, sp1, List.foldl_cons, List.foldl_nil, State.read, gpr_write,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, gpr_setMem, mem_write, mem_setMem, lv_setMem,
      laneA_setMem, hk0, hk1, Size.bits,
      laneA_write _ _ _ (show ¬ Reg.x5 = .x14 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x14 by decide),
      laneA_write _ _ _ (show ¬ Reg.x5 = .x15 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x15 by decide),
      lv_eq]
    rw [readW_writeW_lane mem_R1 hb mem_aA hb (Or.inl (by decide)), lv_eq]
  · simp only [gpr_write, gpr_setMem, h1, h2, ↓reduceIte]

theorem step2_ok {b : Nat} (hb : b < 16) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step2 b) s = some s' ∧ LaneOk s s' sp2 b := by
  rw [step2, runBlock_cons, exec_ldW_lane h mem_tA hb, runStep_some, runBlock_cons,
    exec_stW_lane ?h1 mem_cA hb, runStep_some, runBlock_cons, exec_ldW_lane ?h2 mem_aA hb,
    runStep_some, runBlock_cons, exec_addW, runStep_some, runBlock_cons, exec_stW_lane ?h3 mem_tA hb,
    runStep_some, runBlock_nil]
  case h1 | h2 | h3 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [laneWrites, sp2, List.foldl_cons, List.foldl_nil, State.read, gpr_write,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, gpr_setMem, mem_write, mem_setMem, lv_setMem,
      laneA_setMem, Size.bits,
      laneA_write _ _ _ (show ¬ Reg.x5 = .x14 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x14 by decide),
      laneA_write _ _ _ (show ¬ Reg.x5 = .x15 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x15 by decide),
      lv_eq]
    rw [readW_writeW_lane mem_aA hb mem_cA hb (Or.inl (by decide)), lv_eq]
  · simp only [gpr_write, gpr_setMem, h1, h2, ↓reduceIte]

theorem step3_ok {b : Nat} (hb : b < 16) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step3 b) s = some s' ∧ LaneOk s s' sp3 b := by
  rw [step3, runBlock_cons, exec_ldW_lane h mem_tA hb, runStep_some, runBlock_cons,
    exec_stW_lane ?h1 mem_dA hb, runStep_some, runBlock_cons, exec_ldW_lane ?h2 mem_cA hb,
    runStep_some, runBlock_cons, exec_addW, runStep_some, runBlock_cons, exec_stW_lane ?h3 mem_tA hb,
    runStep_some, runBlock_nil]
  case h1 | h2 | h3 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [laneWrites, sp3, List.foldl_cons, List.foldl_nil, State.read, gpr_write,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, gpr_setMem, mem_write, mem_setMem, lv_setMem,
      laneA_setMem, Size.bits,
      laneA_write _ _ _ (show ¬ Reg.x5 = .x14 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x14 by decide),
      laneA_write _ _ _ (show ¬ Reg.x5 = .x15 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x15 by decide),
      lv_eq]
    rw [readW_writeW_lane mem_cA hb mem_dA hb (Or.inl (by decide)), lv_eq]
  · simp only [gpr_write, gpr_setMem, h1, h2, ↓reduceIte]

theorem step4_ok {b : Nat} (hb : b < 16) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step4 b) s = some s' ∧ LaneOk s s' sp4 b := by
  rw [step4, runBlock_cons, exec_ldW_lane h mem_tA hb, runStep_some, runBlock_cons,
    exec_ldW_lane ?h1 mem_L1 hb, runStep_some, runBlock_cons, exec_eorW, runStep_some,
    runBlock_cons, exec_stW_lane ?h2 mem_L1 hb, runStep_some, runBlock_cons,
    exec_ldW_lane ?h3 mem_dA hb, runStep_some, runBlock_cons, exec_addW, runStep_some,
    runBlock_cons, exec_ldW_lane ?h4 mem_L0 hb, runStep_some, runBlock_cons, exec_eorW, runStep_some,
    runBlock_cons, exec_stW_lane ?h5 mem_L0 hb, runStep_some, runBlock_nil]
  case h1 | h2 | h3 | h4 | h5 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [laneWrites, sp4, List.foldl_cons, List.foldl_nil, State.read, gpr_write,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, gpr_setMem, mem_write, mem_setMem, lv_setMem,
      laneA_setMem, Size.bits,
      laneA_write _ _ _ (show ¬ Reg.x5 = .x14 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x14 by decide),
      laneA_write _ _ _ (show ¬ Reg.x5 = .x15 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x15 by decide),
      lv_eq]
    rw [readW_writeW_lane mem_dA hb mem_L1 hb (Or.inl (by decide)),
      readW_writeW_lane mem_L0 hb mem_L1 hb (Or.inl (by decide)), lv_eq, lv_eq]
  · simp only [gpr_write, gpr_setMem, h1, h2, ↓reduceIte]

end VG.Proof.Seed.AArch64
