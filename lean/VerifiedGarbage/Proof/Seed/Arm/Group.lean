module

import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Seed.Arm.Ecb
public import VerifiedGarbage.Proof.Framework.Arm.Straight
public import VerifiedGarbage.Proof.Seed.Rounds
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Seed.Arm.Lanes

/-! ### `Seed.Arm.Prologue`, which this module and modules that import it used -/

section

/-! ### `Seed.Arm.Crypt8`, which this module and modules that import it used -/

section

/-! ### `Seed.Arm.Round`, which this module and modules that import it used -/

section

/-! ### `Seed.Arm.Steps`, which this module and modules that import it used -/

section

/-!
# The steps of a round, lane by lane

As on AArch64 (`Proof/Seed/AArch64/Round.lean`): each step of the round
(`step1` … `step4`) on one lane meets its `LaneSpec` (`LaneOk`); `lanes_ok`
then gives it on all eight. The halves `L` and `R` are at `l` and `r`, the
arrays of `L0`/`R0`, whose second words are 8 slots on.
-/

@[expose] public section

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

/-- The round key's halves are in `u7` and `lr`. -/
def KeysIn (k0 k1 : BitVec 32) (s : State) : Prop := Room s ∧ s.gpr .r12 = k0 ∧ s.gpr .lr = k1

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

end

end

/-!
# A round on ARMv7

`g8_lanes` restates `g8_ok` on the lanes of the arrays, and `round_ok` puts
the steps of a round together: on every lane, `round l r`, with `L` at `l`
and `R` at `r`, does RFC 4269 §2's round (`Spec.Seed.round`, which then
exchanges the halves) to `(L0, L1, R0, R1)`, with the round key in the
slots `k` and `k + 1`, at `kp`: the new `L` is the old `R`, at `r`, and the
new `R` is at `l` (`quadAt`).
-/

@[expose] public section

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Seed.Arm
open VG.Impl.Aes.Arm (sb t0 t1 u7 kp ldS stS eorR)
open VG.Arm.Straight (wordAddr Ok slotRegion add_ofNat_ofNat)
open VG.Proof.Aes.Arm (layerWrites)

theorem room_ok_gCfg {s : State} (h : Room s) : Ok gCfg s where
  slotIn k hk := ⟨_, h.mem, slot_in h (by simp [gCfg] at hk; rw [slots_eq]; omega_arith)⟩
  extIn k hk := by simp [gCfg] at hk
  slots := by have := h.fit; simp [gCfg, slots_eq] at this ⊢; omega_arith
  sep k _ j hj := by simp [gCfg] at hj

/-- `g8` on the lanes: `G` of `G`'s words, the other arrays and the slots
from the arrays' kept. -/
theorem g8_lanes {s : State} (h : Room s) :
    ∃ s', runBlock isa g8 s = some s' ∧
      (∀ w < 8, lv s' (tSlot 0) w = Spec.Seed.g (lv s (tSlot 0) w)) ∧
      (∀ k, 56 ≤ k → k < slots → slotW s' k = slotW s k) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧ Frame [workR s] s.mem s'.mem := by
  obtain ⟨s', hs', hg, hrd, hwr, hsp, hregs, hfr⟩ := g8_ok (room_ok_gCfg h)
  obtain hsb : s'.gpr sb = s.gpr sb := hregs _ (by decide)
  obtain hf := h.fit; rw [slots_eq] at hf
  have := toNat_addr (s.gpr sb)
  refine ⟨s', hs', fun w hw => ?_, fun k hk1 hk2 => ?_, h.congr hsb hwr, hrd, hwr, hsp, hregs, ?_⟩
  · rw [lv, lv, ← tSlot_lane]; exact hg w hw
  · rw [slots_eq] at hk2
    simp only [slotW, hsb]
    refine hfr.readW (r := ⟨wordAddr (s.gpr sb) k, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [slot_addr (by omega_arith)]
    exact Offset.disjoint_base _ (by simp [gCfg]; omega_arith) (by omega_arith)
  · refine hfr.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Region.sub_prefix (by simp [gCfg, tailSlot])⟩

/-! ## The round -/

/-- Lane `b` of the blocks' state, `L` at `l` and `R` at `r`: `(L0, L1, R0, R1)`. -/
def quadAt (s : State) (l r b : Nat) :
    Spec.Seed.Word × Spec.Seed.Word × Spec.Seed.Word × Spec.Seed.Word :=
  (lv s l b, lv s (l + 8) b, lv s r b, lv s (r + 8) b)

theorem reads1 {r : Nat} (hr : r ∈ halves) (k0 k1 : BitVec 32) : ReadsArrays (sp1 r k0 k1) := by
  obtain ⟨hR, hR8, -⟩ := half_mem hr
  intro kv hkv x y h
  simp only [sp1, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ hR, h _ hR8]

theorem reads2 : ReadsArrays sp2 := by
  intro kv hkv x y h
  simp only [sp2, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_aA]

theorem reads3 : ReadsArrays sp3 := by
  intro kv hkv x y h
  simp only [sp3, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_cA]

theorem reads4 {l : Nat} (hl : l ∈ halves) : ReadsArrays (sp4 l) := by
  obtain ⟨hL, hL8, -⟩ := half_mem hl
  intro kv hkv x y h
  simp only [sp4, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_dA, h _ hL, h _ hL8]

theorem dests1 {r : Nat} (k0 k1 : BitVec 32) : ∀ kv ∈ sp1 r k0 k1, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp1, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl
  · exact mem_aA
  · exact mem_tA
theorem dests2 : ∀ kv ∈ sp2, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp2, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl <;> decide
theorem dests3 : ∀ kv ∈ sp3, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp3, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl <;> decide
theorem dests4 {l : Nat} (hl : l ∈ halves) : ∀ kv ∈ sp4 l, kv.1 ∈ arrays := by
  obtain ⟨hL, hL8, -⟩ := half_mem hl
  intro kv hkv; simp only [sp4, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl
  · exact hL8
  · exact hL

/-- A step on all eight lanes, from a state where the scratch buffer is writable. -/
theorem lanes8_room {f : Nat → List Instr} {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays)
    (hd : ReadsArrays sp)
    (hf : ∀ b < 8, ∀ s, Room s → ∃ s', runBlock isa (f b) s = some s' ∧ LaneOk s s' sp b)
    {s : State} (h : Room s) :
    ∃ s', runBlock isa (lanes8 f) s = some s' ∧ Room s' ∧
      (∀ k ∈ arrays, ∀ b < 8, lv s' k b = newVal sp k (fun k' => lv s k' b)) ∧
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) := by
  obtain ⟨s', hs', hP, hv, rest⟩ := lanes_ok hsp hd (P := Room)
    (fun _ s s' hP hok => hP.congr (hok.regs _ (by decide) (by decide)) hok.wr) (fun _ h => h) hf h 8
    (Nat.le_refl _)
  exact ⟨s', hs', hP, fun k hk b hb => by rw [hv k hk b hb, ite_eq_left hb], rest⟩

theorem work_of_arrays {s s' : State} (hfr : Frame [arraysR s] s.mem s'.mem) :
    Frame [workR s] s.mem s'.mem :=
  hfr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, arraysR_sub_work s⟩

theorem runBlock_trans {a b : List Instr} {s s' s'' : State} (h1 : runBlock isa a s = some s')
    (h2 : runBlock isa b s' = some s'') : runBlock isa (a ++ b) s = some s'' := by
  rw [runBlock_append, h1, Option.bind_some, h2]

/-- A slot from the arrays' end on is kept by a frame of the working area. -/
theorem slot_keep_work {s s' : State} (h : Room s) (hfr : Frame [workR s] s.mem s'.mem)
    (hsb : s'.gpr sb = s.gpr sb) {k : Nat} (hk1 : tailSlot ≤ k) (hk2 : k < slots) :
    slotW s' k = slotW s k := by
  obtain hf := h.fit; rw [slots_eq] at hf hk2
  have := toNat_addr (s.gpr sb)
  simp only [slotW, hsb]
  refine hfr.readW (r := ⟨wordAddr (s.gpr sb) k, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rw [slot_addr (by omega_arith)]
  exact Offset.disjoint_base _ (by simp [tailSlot] at hk1 ⊢; omega_arith) (by omega_arith)

theorem keepRegs : ∀ r ∈ [Reg.r8, .r9], r ≠ t0 ∧ r ≠ t1 ∧ r ∉ layerWrites := by decide

/-- The round key at `kp`, slots `k` and `k + 1`. -/
def KeyAt (s : State) (k : Nat) : Prop := s.gpr kp = s.gpr sb + BitVec.ofNat 32 (4 * k)

theorem round_ok {l r : Nat} (hl : l ∈ halves) (hr : r ∈ halves) (hlr : l ≠ r) {s : State} (h : Room s)
    {k : Nat} (hk2 : k + 1 < slots) (hkp : KeyAt s k) :
    ∃ s', runBlock isa (round l r) s = some s' ∧
      (∀ b < 8, quadAt s' r l b = Spec.Seed.round (slotW s k, slotW s (k + 1)) (quadAt s l r b)) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.gpr kp = s.gpr kp + 8 ∧ s'.gpr sb = s.gpr sb ∧
      (∀ j, tailSlot ≤ j → j < slots → slotW s' j = slotW s j) ∧
      Frame [workR s] s.mem s'.mem := by
  obtain hf := h.fit; rw [slots_eq] at hf hk2
  have hT : tailSlot = 112 := rfl
  let K0 := slotW s k
  let K1 := slotW s (k + 1)
  obtain ⟨hL, hL8, hLt, hLa, hLc, hLd, hL8t, hL8a, hL8c, hL8d, hLL⟩ := half_mem hl
  obtain ⟨hR, hR8, hRt, hRa, hRc, hRd, hR8t, hR8a, hR8c, hR8d, hRR⟩ := half_mem hr
  obtain hlr8 : l ≠ r + 8 ∧ l + 8 ≠ r ∧ l + 8 ≠ r + 8 := by
    simp only [halves, List.mem_cons, List.not_mem_nil, or_false] at hl hr
    rcases hl with rfl | rfl <;> rcases hr with rfl | rfl <;> first | exact absurd rfl hlr | decide
  -- The round key.
  obtain ek : ∀ d, d = 0 ∨ d = 4 → s.gpr kp + BitVec.ofNat 32 d = s.gpr sb + BitVec.ofNat 32 (4 * (k + d / 4)) := by
    intro d hd
    rw [hkp, add_ofNat_ofNat]; rcases hd with rfl | rfl <;> rfl
  obtain e1 : exec (.ldr u7 kp 0) s = some (s.setReg u7 K0) := by
    rw [exec_ldr (by decide) (by rw [ek 0 (.inl rfl)]; exact ⟨_, List.mem_append_right _ h.mem,
      slot_in h (by rw [slots_eq]; omega_arith)⟩), ek 0 (.inl rfl)]; rfl
  obtain e2 : exec (.ldr .lr kp 4) (s.setReg u7 K0) = some ((s.setReg u7 K0).setReg .lr K1) := by
    rw [exec_ldr (by decide) (by
      rw [gpr_setReg_of_ne _ _ (by decide), ek 4 (.inr rfl), rd_setReg, wr_setReg]
      exact ⟨_, List.mem_append_right _ h.mem, slot_in h (by rw [slots_eq]; omega_arith)⟩),
      gpr_setReg_of_ne _ _ (by decide), ek 4 (.inr rfl), mem_setReg]; rfl
  let s2 := (s.setReg u7 K0).setReg .lr K1
  obtain hrun2 : runBlock isa [.ldr u7 kp 0, .ldr .lr kp 4] s = some s2 := by
    rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_nil]
  obtain g2 : ∀ r, r ≠ u7 → r ≠ .lr → s2.gpr r = s.gpr r := fun r h1 h2 => by
    simp only [s2, gpr_setReg_of_ne _ _ h1, gpr_setReg_of_ne _ _ h2]
  obtain h2 : Room s2 := room_setReg (room_setReg h (by decide) _) (by decide) _
  obtain hkeys : KeysIn K0 K1 s2 := ⟨h2, by
      show ((s.setReg u7 K0).setReg .lr K1).gpr u7 = K0
      rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_self], gpr_setReg_self _ _ _⟩
  obtain lv2 : ∀ k b, lv s2 k b = lv s k b := fun k b => by
    simp only [lv, s2, slotW_setReg _ (show (Reg.lr) ≠ sb by decide), slotW_setReg _ (show u7 ≠ sb by decide)]
  -- The steps.
  obtain ⟨s3, hs3, hP3, hv3, fr3, rd3, wr3, spp3, rg3⟩ := lanes_ok (dests1 (r := r) K0 K1) (reads1 hr K0 K1)
    (P := KeysIn K0 K1)
    (fun _ s s' hP hok => ⟨hP.1.congr (hok.regs _ (by decide) (by decide)) hok.wr,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.1,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.2⟩)
    (fun _ h => h.1) (fun b hb s hs => step1_ok hr K0 K1 hb s hs) hkeys 8 (Nat.le_refl _)
  obtain ⟨s4, hs4, hg4, hk4, h4, rd4, wr4, spp4, rg4, fr4⟩ := g8_lanes hP3.1
  obtain ⟨s5, hs5, h5, hv5, fr5, rd5, wr5, spp5, rg5⟩ :=
    lanes8_room dests2 reads2 (fun b hb s hs => step2_ok hb s hs) h4
  obtain ⟨s6, hs6, hg6, hk6, h6, rd6, wr6, spp6, rg6, fr6⟩ := g8_lanes h5
  obtain ⟨s7, hs7, h7, hv7, fr7, rd7, wr7, spp7, rg7⟩ :=
    lanes8_room dests3 reads3 (fun b hb s hs => step3_ok hb s hs) h6
  obtain ⟨s8, hs8, hg8, hk8, h8, rd8, wr8, spp8, rg8, fr8⟩ := g8_lanes h7
  obtain ⟨s9, hs9, h9, hv9, fr9, rd9, wr9, spp9, rg9⟩ :=
    lanes8_room (dests4 hl) (reads4 hl) (fun b hb s hs => step4_ok hl hb s hs) h8
  let s10 := s9.setReg kp (s9.gpr kp + 8)
  obtain hrun : runBlock isa [.dp .add kp kp (.imm 8)] s9 = some s10 := by
    rw [runBlock_cons, show exec (.dp .add kp kp (.imm 8)) s9 = some s10 by simp [exec, Op2.eval, s10]; decide,
      runStep_some, runBlock_nil]
  -- Registers through the steps.
  obtain keep : ∀ r ∈ [Reg.r8, .r9], s9.gpr r = s.gpr r := by
    intro r hr
    obtain ⟨h1, h2, hg⟩ := keepRegs r hr
    obtain h3 : r ≠ u7 ∧ r ≠ .lr := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide
    rw [rg9 r h1 h2, rg8 r hg, rg7 r h1 h2, rg6 r hg, rg5 r h1 h2, rg4 r hg, rg3 r h1 h2, g2 r h3.1 h3.2]
  obtain sb9 : s9.gpr sb = s.gpr sb := keep _ (by decide)
  obtain sb10 : s10.gpr sb = s.gpr sb := by rw [gpr_setReg_of_ne _ _ (by decide), sb9]
  obtain lv10 : ∀ k b, lv s10 k b = lv s9 k b := fun k b => slotW_setReg _ (by decide) _ _
  -- The working area's frames.
  obtain fc : ∀ {t : State} {m m' : Mem}, t.gpr sb = s.gpr sb → Frame [workR t] m m' →
      Frame [workR s] m m' := fun ht hf => by simpa [workR, ht] using hf
  obtain sb3 : s3.gpr sb = s.gpr sb := by rw [rg3 _ (by decide) (by decide), g2 _ (by decide) (by decide)]
  obtain sb4 : s4.gpr sb = s.gpr sb := by rw [rg4 _ (by decide), sb3]
  obtain sb5 : s5.gpr sb = s.gpr sb := by rw [rg5 _ (by decide) (by decide), sb4]
  obtain sb6 : s6.gpr sb = s.gpr sb := by rw [rg6 _ (by decide), sb5]
  obtain sb7 : s7.gpr sb = s.gpr sb := by rw [rg7 _ (by decide) (by decide), sb6]
  obtain sb8 : s8.gpr sb = s.gpr sb := by rw [rg8 _ (by decide), sb7]
  obtain frame : Frame [workR s] s.mem s10.mem := by
    simp only [s10, mem_setReg]
    refine (fc (g2 _ (by decide) (by decide)) (work_of_arrays fr3)).trans ?_
    refine (fc sb3 fr4).trans ?_
    refine (fc sb4 (work_of_arrays fr5)).trans ?_
    refine (fc sb5 fr6).trans ?_
    refine (fc sb6 (work_of_arrays fr7)).trans ?_
    refine (fc sb7 fr8).trans ?_
    exact fc sb8 (work_of_arrays fr9)
  refine ⟨s10, ?_, fun b hb => ?_, h9.congr (gpr_setReg_of_ne _ _ (by decide)) rfl, ?_, ?_, ?_, ?_, sb10, fun j hj1 hj2 => ?_, frame⟩
  · exact runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans
      (runBlock_trans (runBlock_trans (runBlock_trans hrun2 hs3) hs4) hs5) hs6) hs7) hs8) hs9) hrun
  · -- The values, stage by stage.
    obtain t3 : lv s3 (tSlot 0) b = (lv s r b ^^^ K0) ^^^ (lv s (r + 8) b ^^^ K1) := by
      rw [hv3 _ mem_tA b hb, ite_eq_left hb]
      simp [newVal, sp1, lv2, tSlot, aSlot, BitVec.xor_assoc]
    obtain a3 : lv s3 aSlot b = lv s r b ^^^ K0 := by
      rw [hv3 _ mem_aA b hb, ite_eq_left hb]
      simp [newVal, sp1, lv2, tSlot, aSlot]
    obtain o3 : ∀ k ∈ [l, l + 8, r, r + 8], lv s3 k b = lv s k b := by
      intro k hk
      obtain hk' : k ∈ arrays ∧ k ≠ aSlot ∧ k ≠ tSlot 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl
        exacts [⟨hL, hLa, hLt⟩, ⟨hL8, hL8a, hL8t⟩, ⟨hR, hRa, hRt⟩, ⟨hR8, hR8a, hR8t⟩]
      rw [hv3 _ hk'.1 b hb, ite_eq_left hb]
      simp [newVal, sp1, lv2, Ne.symm hk'.2.1, Ne.symm hk'.2.2]
    -- c
    obtain k4 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s4 k b = lv s3 k b := fun k hk hkt => by
      have := arrays_bound k hk
      obtain hk56 : 56 ≤ k := by
        simp only [arrays, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hkt | decide
      exact hk4 _ (by omega_arith) (by rw [slots_eq]; omega_arith)
    obtain t5 : lv s5 (tSlot 0) b = lv s4 (tSlot 0) b + lv s4 aSlot b := by
      rw [hv5 _ mem_tA b hb]; simp [newVal, sp2, tSlot, cSlot]
    obtain c5 : lv s5 cSlot b = lv s4 (tSlot 0) b := by
      rw [hv5 _ mem_cA b hb]; simp [newVal, sp2, tSlot, cSlot]
    obtain o5 : ∀ k ∈ arrays, k ≠ tSlot 0 → k ≠ cSlot → lv s5 k b = lv s4 k b := by
      intro k hk h1 h2; rw [hv5 _ hk b hb]; simp [newVal, sp2, Ne.symm h1, Ne.symm h2]
    -- d
    obtain k6 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s6 k b = lv s5 k b := fun k hk hkt => by
      have := arrays_bound k hk
      obtain hk56 : 56 ≤ k := by
        simp only [arrays, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hkt | decide
      exact hk6 _ (by omega_arith) (by rw [slots_eq]; omega_arith)
    obtain t7 : lv s7 (tSlot 0) b = lv s6 (tSlot 0) b + lv s6 cSlot b := by
      rw [hv7 _ mem_tA b hb]; simp [newVal, sp3, tSlot, dSlot]
    obtain d7 : lv s7 dSlot b = lv s6 (tSlot 0) b := by
      rw [hv7 _ mem_dA b hb]; simp [newVal, sp3, tSlot, dSlot]
    obtain o7 : ∀ k ∈ arrays, k ≠ tSlot 0 → k ≠ dSlot → lv s7 k b = lv s6 k b := by
      intro k hk h1 h2; rw [hv7 _ hk b hb]; simp [newVal, sp3, Ne.symm h1, Ne.symm h2]
    -- e
    obtain k8 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s8 k b = lv s7 k b := fun k hk hkt => by
      have := arrays_bound k hk
      obtain hk56 : 56 ≤ k := by
        simp only [arrays, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hkt | decide
      exact hk8 _ (by omega_arith) (by rw [slots_eq]; omega_arith)
    obtain l0_9 : lv s9 l b = (lv s8 (tSlot 0) b + lv s8 dSlot b) ^^^ lv s8 l b := by
      rw [hv9 _ hL b hb]; simp [newVal, sp4]
    obtain l1_9 : lv s9 (l + 8) b = lv s8 (l + 8) b ^^^ lv s8 (tSlot 0) b := by
      rw [hv9 _ hL8 b hb]; simp [newVal, sp4]
    obtain r0_9 : lv s9 r b = lv s8 r b := by
      rw [hv9 _ hR b hb]; simp [newVal, sp4, hlr, hlr8.2.1]
    obtain r1_9 : lv s9 (r + 8) b = lv s8 (r + 8) b := by
      rw [hv9 _ hR8 b hb]; simp [newVal, sp4, hlr8.1, hlr]
    -- The halves, through the `G`s and the steps that do not write them.
    obtain xs : ∀ k ∈ [l, l + 8, r, r + 8], lv s8 k b = lv s k b := by
      intro k hk
      obtain hk' : k ∈ arrays ∧ k ≠ tSlot 0 ∧ k ≠ cSlot ∧ k ≠ dSlot := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl
        exacts [⟨hL, hLt, hLc, hLd⟩, ⟨hL8, hL8t, hL8c, hL8d⟩, ⟨hR, hRt, hRc, hRd⟩, ⟨hR8, hR8t, hR8c, hR8d⟩]
      rw [k8 k hk'.1 hk'.2.1, o7 k hk'.1 hk'.2.1 hk'.2.2.2, k6 k hk'.1 hk'.2.1, o5 k hk'.1 hk'.2.1 hk'.2.2.1,
        k4 k hk'.1 hk'.2.1, o3 k hk]
    obtain t4 : lv s4 (tSlot 0) b = Spec.Seed.g (lv s3 (tSlot 0) b) := hg4 b hb
    obtain t6 : lv s6 (tSlot 0) b = Spec.Seed.g (lv s5 (tSlot 0) b) := hg6 b hb
    obtain t8 : lv s8 (tSlot 0) b = Spec.Seed.g (lv s7 (tSlot 0) b) := hg8 b hb
    obtain a4 : lv s4 aSlot b = lv s3 aSlot b := k4 _ mem_aA (by decide)
    obtain c6 : lv s6 cSlot b = lv s5 cSlot b := k6 _ mem_cA (by decide)
    obtain d8 : lv s8 dSlot b = lv s7 dSlot b := k8 _ mem_dA (by decide)
    simp only [quadAt, lv10, r0_9, r1_9, l0_9, l1_9]
    simp only [xs l (by simp), xs (l + 8) (by simp), xs r (by simp), xs (r + 8) (by simp), d8, d7, t8, t7,
      c6, c5, t6, t5, t4, a4, a3, t3]
    simp only [Spec.Seed.round, Spec.Seed.f, K0, K1, BitVec.xor_comm (lv s l b),
      BitVec.xor_comm (lv s (l + 8) b)]
  · simp only [s10, rd_setReg, rd9, rd8, rd7, rd6, rd5, rd4, rd3]; rfl
  · simp only [s10, wr_setReg, wr9, wr8, wr7, wr6, wr5, wr4, wr3]; rfl
  · simp only [s10, sp_setReg, spp9, spp8, spp7, spp6, spp5, spp4, spp3]; rfl
  · rw [show s10.gpr kp = s9.gpr kp + 8 from gpr_setReg_self _ _ _, show s9.gpr kp = s.gpr kp from keep _ (by decide)]
  · rw [show slotW s10 j = slotW s9 j from slotW_setReg _ (by decide) _ _]
    exact slot_keep_work h (by simpa only [s10, mem_setReg] using frame) sb9 hj1 hj2

end VG.Proof.Seed.Arm

end

end

/-!
# Eight blocks of SEED on ARMv7

`crypt8_wp`: `crypt8` turns each of the eight blocks of the tail buffer into
`Spec.Seed.crypt` of it, with round `j + 1`'s key in the table's slots
`tableSlot + 2j` and `tableSlot + 2j + 1` (`tableKeys`). It copies the
blocks' words, byte-reversed, to the arrays (`toArr`, by `moves_ok`), runs
the eight pairs of rounds (`rounds_wp`), and copies the arrays back, `R`
first (`fromArr`).
-/

@[expose] public section

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Seed.Arm VG.Proof.Seed
open VG.Impl.Aes.Arm (sb t0 t1 u7 kp ldS stS eorR)
open VG.Arm.Straight (wordAddr add_ofNat_ofNat)

/-! ## Single instructions -/

/-- `add d, n, #v` (`v` encodable). -/
theorem addImm_ok (s : State) (d n : Reg) (v : BitVec 32) (hv : encodable v = true) :
    ∃ s', runBlock isa [.dp .add d n (.imm v)] s = some s' ∧ s'.gpr d = s.gpr n + v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d (s.gpr n + v), by
    rw [runBlock_cons, show exec (.dp .add d n (.imm v)) s = some (s.setReg d (s.gpr n + v)) by
      simp [exec, Op2.eval, hv], runStep_some, runBlock_nil],
    gpr_setReg_self _ _ _, fun r hr => gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-- `sub t0, kp, sb; cmp t0, #v`. -/
theorem endTest_ok (s : State) (v : BitVec 32) (hv : encodable v = true) :
    ∃ s', runBlock isa [.dp .sub t0 kp (.reg sb), .cmp t0 (.imm v)] s = some s' ∧
      s'.z = (s.gpr kp - s.gpr sb - v == 0) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₁ := s.setReg t0 (s.gpr kp - s.gpr sb)
  refine ⟨subFlags s₁ (s.gpr kp - s.gpr sb) v, ?_, by simp [subFlags], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [runBlock_cons, show exec (.dp .sub t0 kp (.reg sb)) s = some s₁ from rfl, runStep_some, runBlock_cons,
      show exec (.cmp t0 (.imm v)) s₁ = some (subFlags s₁ (s.gpr kp - s.gpr sb) v) by
        simp [exec, Op2.eval, hv, s₁, gpr_setReg_self],
      runStep_some, runBlock_nil]
  · simp [subFlags, s₁, gpr_setReg_of_ne _ _ hr]

theorem ofNat32_sub_beq {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl
theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

/-! ## Moving words between slots, byte-reversed -/

/-- `ldr t0, [sb, #4 a]; rev t0, t0; str t0, [sb, #4 d]` for each `(a, d)`. -/
def movesCode (L : List (Nat × Nat)) : List Instr := L.flatMap fun p => [ldS t0 p.1, .rev t0 t0, stS p.2 t0]

theorem moves_ok {s : State} (h : Room s) {n : Nat} (hn : n ≤ slots) :
    ∀ (L : List (Nat × Nat)), (∀ p ∈ L, p.1 < slots ∧ p.2 < n) → (∀ p ∈ L, ∀ q ∈ L, p.1 ≠ q.2) →
      (L.map (·.2)).Nodup →
      ∃ s', runBlock isa (movesCode L) s = some s' ∧
        (∀ p ∈ L, slotW s' p.2 = byteRev32 (slotW s p.1)) ∧
        (∀ j < slots, j ∉ L.map (·.2) → slotW s' j = slotW s j) ∧
        (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        Frame [⟨State.addr (s.gpr sb), 4 * n⟩] s.mem s'.mem
  | [], _, _, _ => ⟨s, runBlock_nil, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | p :: L, hL, hd, hnd => by
    have hp := hL p List.mem_cons_self
    have hpd : p.2 < slots := by omega_arith
    let s₁ := setMem ((s.setReg t0 (slotW s p.1)).setReg t0 (rev (slotW s p.1)))
      (s.mem.writeW (slotA s p.2) (rev (slotW s p.1)))
    have e₁ : runBlock isa [ldS t0 p.1, .rev t0 t0, stS p.2 t0] s = some s₁ := by
      rw [runBlock_cons, exec_ldS h hp.1, runStep_some, runBlock_cons,
        show exec (.rev t0 t0) (s.setReg t0 (slotW s p.1)) =
          some ((s.setReg t0 (slotW s p.1)).setReg t0 (rev (slotW s p.1))) by
          simp [exec, gpr_setReg_self],
        runStep_some, runBlock_cons,
        exec_stS (room_setReg (room_setReg h (by decide) _) (by decide) _) hpd, runStep_some, runBlock_nil]
      simp only [s₁, slotA_setReg _ (show t0 ≠ sb by decide), gpr_setReg_self, mem_setReg]
    have h₁ : Room s₁ := room_setMem (room_setReg (room_setReg h (by decide) _) (by decide) _) _
    have sb₁ : s₁.gpr sb = s.gpr sb := by
      simp only [s₁, gpr_setMem, gpr_setReg_of_ne _ _ (show sb ≠ t0 by decide)]
    have sl₁ : ∀ j < slots, slotW s₁ j = if j = p.2 then rev (slotW s p.1) else slotW s j := by
      intro j hj
      rw [show s₁ = setMem _ _ from rfl, slotW_setMem, slotA_setReg _ (by decide), slotA_setReg _ (by decide)]
      exact slotW_setMem_write h hpd hj _
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', o', g', rd', wr', sp', f'⟩ := moves_ok h₁ hn L (fun q hq => hL q (List.mem_cons_of_mem _ hq))
      (fun q hq q' hq' => hd q (List.mem_cons_of_mem _ hq) q' (List.mem_cons_of_mem _ hq')) hnd.2
    have hfit := h.fit
    refine ⟨s', ?_, fun q hq => ?_, fun j hj hjL => ?_, fun r hr => ?_, by rw [rd']; rfl, by rw [wr']; rfl,
      by rw [sp']; rfl, ?_⟩
    · rw [movesCode, List.flatMap_cons, runBlock_append, e₁, Option.bind_some]; exact e'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [o' _ (by have := (hL q List.mem_cons_self).2; omega_arith) hnd.1, sl₁ _ hpd, ite_eq_left rfl]; rfl
      · rw [v' q hq, sl₁ _ (hL q (List.mem_cons_of_mem _ hq)).1,
          ite_eq_right (hd q (List.mem_cons_of_mem _ hq) p List.mem_cons_self)]
    · simp only [List.map_cons, List.mem_cons, not_or] at hjL
      rw [o' j hj hjL.2, sl₁ j hj, ite_eq_right hjL.1]
    · rw [g' r hr]
      simp only [s₁, gpr_setMem, gpr_setReg_of_ne _ _ hr]
    · refine Frame.trans ?_ (by rw [sb₁] at f'; exact f')
      show Frame _ s.mem (s.mem.writeW (slotA s p.2) (rev (slotW s p.1)))
      refine (Frame.refl _ _).writeW List.mem_cons_self _ ?_
      rw [slots_eq] at hfit hn
      exact Straight.slot_contains _ hp.2 (by omega_arith)

/-! ## The blocks and the arrays -/

/-- Block `b` of the tail buffer. -/
abbrev tailBlock (s : State) (b : Nat) : Spec.Seed.Block :=
  Spec.Seed.blockAt s.mem (State.addr (s.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * b))

def toArrMoves : List (Nat × Nat) :=
  (List.range 8).flatMap fun b => (List.range 4).map fun w => (tailAt b w, arrSlot w + b)

def fromArrMoves : List (Nat × Nat) :=
  (List.range 8).flatMap fun b => (List.range 4).map fun w => (arrSlot ((w + 2) % 4) + b, tailAt b w)

theorem toArr_eq : toArr = movesCode toArrMoves := by decide +kernel
theorem fromArr_eq : fromArr = movesCode fromArrMoves := by decide +kernel

theorem toArr_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa toArr s = some s' ∧
      (∀ w < 4, ∀ b < 8, lv s' (arrSlot w) b = byteRev32 (slotW s (tailAt b w))) ∧
      (∀ j < slots, tailSlot ≤ j → slotW s' j = slotW s j) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [workR s] s.mem s'.mem := by
  obtain ⟨s', e', v', o', g', rd', wr', sp', f'⟩ := moves_ok h (n := tailSlot) (by decide) toArrMoves
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨s', ?_, fun w hw b hb => ?_, fun j hj1 hj2 => o' j hj1 ?_, g', rd', wr', sp', f'⟩
  · rw [toArr_eq]; exact e'
  · exact v' (tailAt b w, arrSlot w + b)
      (by simp only [toArrMoves, List.mem_flatMap, List.mem_map, List.mem_range]; exact ⟨b, hb, w, hw, rfl⟩)
  · intro hm
    simp only [toArrMoves, List.map_flatMap, List.map_map, List.mem_flatMap, List.mem_map, List.mem_range,
      Function.comp] at hm
    obtain ⟨b, hb, w, hw, rfl⟩ := hm
    have : arrSlot w + b < tailSlot := by simp [arrSlot, tailSlot]; omega_arith
    omega_arith

theorem fromArr_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa fromArr s = some s' ∧
      (∀ w < 4, ∀ b < 8, slotW s' (tailAt b w) = byteRev32 (lv s (arrSlot ((w + 2) % 4)) b)) ∧
      (∀ j < slots, tableSlot ≤ j → slotW s' j = slotW s j) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr (s.gpr sb), 4 * tableSlot⟩] s.mem s'.mem := by
  obtain ⟨s', e', v', o', g', rd', wr', sp', f'⟩ := moves_ok h (n := tableSlot) (by decide) fromArrMoves
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨s', ?_, fun w hw b hb => ?_, fun j hj1 hj2 => o' j hj1 ?_, g', rd', wr', sp', f'⟩
  · rw [fromArr_eq]; exact e'
  · exact v' (arrSlot ((w + 2) % 4) + b, tailAt b w)
      (by simp only [fromArrMoves, List.mem_flatMap, List.mem_map, List.mem_range]; exact ⟨b, hb, w, hw, rfl⟩)
  · intro hm
    simp only [fromArrMoves, List.map_flatMap, List.map_map, List.mem_flatMap, List.mem_map, List.mem_range,
      Function.comp] at hm
    obtain ⟨b, hb, w, hw, rfl⟩ := hm
    have : tailAt b w < tableSlot := by simp [tailAt, tailSlot, tableSlot]; omega_arith
    omega_arith

/-! ## The rounds -/

/-- Round `j + 1`'s key, in the table of `s`. -/
def tableKeys (s : State) (j : Nat) : Spec.Seed.Word × Spec.Seed.Word :=
  (slotW s (tableSlot + 2 * j), slotW s (tableSlot + 2 * j + 1))

theorem halves0 : arrSlot 0 ∈ halves := by decide
theorem halves2 : arrSlot 2 ∈ halves := by decide

/-- Two rounds, the round keys in the slots from `k`, and the end test. -/
theorem roundPair_ok {s : State} (h : Room s) {k : Nat} (hk : k + 4 ≤ tableEnd) (hk0 : tableSlot ≤ k)
    (hkp : KeyAt s k) :
    ∃ s', runBlock isa roundPair s = some s' ∧
      (∀ b < 8, quadAt s' (arrSlot 0) (arrSlot 2) b = Spec.Seed.round (slotW s (k + 2), slotW s (k + 3))
        (Spec.Seed.round (slotW s k, slotW s (k + 1)) (quadAt s (arrSlot 0) (arrSlot 2) b))) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ KeyAt s' (k + 4) ∧ s'.gpr sb = s.gpr sb ∧
      (∀ j, tailSlot ≤ j → j < slots → slotW s' j = slotW s j) ∧ Frame [workR s] s.mem s'.mem ∧
      s'.z = decide (k + 4 = tableEnd) := by
  have hT : tableEnd = 176 := rfl
  have hS : tableSlot = 144 := rfl
  obtain ⟨s₁, e₁, q₁, h₁, rd₁, wr₁, sp₁, kp₁, sb₁, sl₁, f₁⟩ :=
    round_ok halves0 halves2 (by decide) h (k := k) (by rw [slots_eq]; omega_arith) hkp
  have hkp₁ : KeyAt s₁ (k + 2) := by
    rw [KeyAt, kp₁, hkp, sb₁, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_ofNat]
    rfl
  obtain ⟨s₂, e₂, q₂, h₂, rd₂, wr₂, sp₂, kp₂, sb₂, sl₂, f₂⟩ :=
    round_ok halves2 halves0 (by decide) h₁ (k := k + 2) (by rw [slots_eq]; omega_arith) hkp₁
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃, sp₃⟩ := endTest_ok s₂ (BitVec.ofNat 32 (4 * tableEnd)) (by decide)
  have sb₃ : s₃.gpr sb = s.gpr sb := by rw [g₃ _ (by decide), sb₂, sb₁]
  have hkp₂ : s₂.gpr kp = s.gpr sb + BitVec.ofNat 32 (4 * (k + 4)) := by
    rw [kp₂, hkp₁, sb₁, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_ofNat]
    rfl
  have sl₃ : ∀ j, slotW s₃ j = slotW s₂ j := fun j => by simp only [slotW, m₃, g₃ sb (by decide)]
  have hfit := h.fit
  rw [slots_eq] at hfit
  refine ⟨s₃, ?_, fun b hb => ?_, h₂.congr (g₃ _ (by decide)) wr₃, by rw [rd₃, rd₂, rd₁],
    by rw [wr₃, wr₂, wr₁], by rw [sp₃, sp₂, sp₁], ?_, sb₃, fun j hj1 hj2 => ?_, ?_, ?_⟩
  · rw [roundPair, runBlock_append, runBlock_append, e₁, Option.bind_some, e₂, Option.bind_some, e₃]
  · have e : quadAt s₃ (arrSlot 0) (arrSlot 2) b = quadAt s₂ (arrSlot 0) (arrSlot 2) b := by
      simp only [quadAt, lv, sl₃]
    rw [e, q₂ b hb, q₁ b hb, sl₁ _ (by simp [tailSlot]; omega_arith) (by rw [slots_eq]; omega_arith),
      sl₁ _ (by simp [tailSlot]; omega_arith) (by rw [slots_eq]; omega_arith)]
  · rw [KeyAt, g₃ _ (by decide), hkp₂, sb₃]
  · rw [sl₃, sl₂ j hj1 hj2, sl₁ j hj1 hj2]
  · rw [m₃]; exact f₁.trans (by simpa [workR, sb₁] using f₂)
  · have e2 : s₂.gpr sb = s.gpr sb := by rw [sb₂, sb₁]
    rw [z₃, hkp₂, e2, Offset.add_sub_cancel_left, ofNat32_sub_beq (by omega_arith) (by omega_arith)]
    simp only [decide_eq_decide]; omega_arith

/-- The sixteen rounds, round `j + 1`'s key in the table's slots
`tableSlot + 2j` and `tableSlot + 2j + 1`. -/
theorem rounds_wp {s₀ : State} (h : Room s₀) :
    WP isa rounds s₀ fun s' =>
      (∀ b < 8, quadAt s' (arrSlot 0) (arrSlot 2) b =
        roundsN (tableKeys s₀) 16 (quadAt s₀ (arrSlot 0) (arrSlot 2) b)) ∧
      Room s' ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧ s'.gpr sb = s₀.gpr sb ∧
      (∀ j, tailSlot ≤ j → j < slots → slotW s' j = slotW s₀ j) ∧ Frame [workR s₀] s₀.mem s'.mem := by
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := addImm_ok s₀ kp sb (BitVec.ofNat 32 (4 * tableSlot)) (by decide)
  have sb₁ : s₁.gpr sb = s₀.gpr sb := o₁ _ (by decide)
  have sl₁ : ∀ j, slotW s₁ j = slotW s₀ j := fun j => by simp only [slotW, m₁, sb₁]
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = 8 - m ∧ m < 8 ∧ Room s ∧ s.gpr sb = s₀.gpr sb ∧
    KeyAt s (tableSlot + 4 * m) ∧
    (∀ b < 8, quadAt s (arrSlot 0) (arrSlot 2) b =
      roundsN (tableKeys s₀) (2 * m) (quadAt s₀ (arrSlot 0) (arrSlot 2) b)) ∧
    s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
    (∀ j, tailSlot ≤ j → j < slots → slotW s j = slotW s₀ j) ∧ Frame [workR s₀] s₀.mem s.mem
  refine WP.loop (M := isa) Inv (fun n s hs => ?_) 8 s₁
    ⟨0, rfl, by omega_arith, h.congr sb₁ wr₁, sb₁, by rw [KeyAt, k₁, sb₁]; rfl,
      fun b _ => by simp only [quadAt, lv, sl₁]; rfl, rd₁, wr₁, sp₁, fun j _ _ => sl₁ j,
      by rw [m₁]; exact Frame.refl _ _⟩
  obtain ⟨m, rfl, hm8, hR, hsb, hkp, hq, hrd, hwr, hsp, hsl, hf⟩ := hs
  obtain ⟨s', e', q', R', rd', wr', sp', kp', sb', sl', f', z'⟩ :=
    roundPair_ok hR (k := tableSlot + 4 * m) (by simp [tableEnd]; omega_arith) (by omega_arith) hkp
  have hkeys : ∀ i < 4, slotW s (tableSlot + 4 * m + i) = slotW s₀ (tableSlot + 4 * m + i) := fun i hi =>
    hsl _ (by simp [tailSlot, tableSlot]; omega_arith) (by rw [slots_eq]; simp [tableSlot]; omega_arith)
  have inv' : ∀ b < 8, quadAt s' (arrSlot 0) (arrSlot 2) b =
      roundsN (tableKeys s₀) (2 * (m + 1)) (quadAt s₀ (arrSlot 0) (arrSlot 2) b) := by
    intro b hb
    rw [q' b hb, hq b hb, show 2 * (m + 1) = 2 * m + 1 + 1 by omega_arith, roundsN_succ, roundsN_succ,
      hkeys 2 (by omega_arith), hkeys 3 (by omega_arith), hkeys 1 (by omega_arith),
      show tableSlot + 4 * m = tableSlot + 4 * m + 0 from rfl, hkeys 0 (by omega_arith)]
    simp only [tableKeys]
    rw [show tableSlot + 2 * (2 * m) = tableSlot + 4 * m + 0 by omega_arith,
      show tableSlot + 2 * (2 * m + 1) = tableSlot + 4 * m + 2 by omega_arith,
      show tableSlot + 4 * m + 0 + 1 = tableSlot + 4 * m + 1 by omega_arith,
      show tableSlot + 4 * m + 2 + 1 = tableSlot + 4 * m + 3 by omega_arith]
  refine WP.of_runBlock ⟨s', e', ?_⟩
  have hf' : Frame [workR s₀] s₀.mem s'.mem := hf.trans (by simpa [workR, hsb] using f')
  have hsl' : ∀ j, tailSlot ≤ j → j < slots → slotW s' j = slotW s₀ j := fun j h1 h2 => by
    rw [sl' j h1 h2, hsl j h1 h2]
  by_cases h8 : m + 1 = 8
  · refine .inl ⟨by rw [eval_ne, z']; simp [tableEnd]; omega_arith, fun b hb => ?_, R', by rw [rd', hrd],
      by rw [wr', hwr], by rw [sp', hsp], by rw [sb', hsb], hsl', hf'⟩
    rw [inv' b hb, h8]
  · refine .inr ⟨by rw [eval_ne, z']; simp [tableEnd]; omega_arith, 8 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith,
      R', by rw [sb', hsb], by rw [show tableSlot + 4 * (m + 1) = tableSlot + 4 * m + 4 by omega_arith]; exact kp', inv', by rw [rd', hrd], by rw [wr', hwr], by rw [sp', hsp],
      hsl', hf'⟩

/-! ## Eight blocks -/

/-- Byte `j` (in memory order) of a byte-reversed word is byte `3 - j` of the word. -/
theorem byteRev32_byte (x : BitVec 32) {j : Nat} (hj : j < 4) :
    (byteRev32 x).extractLsb' (8 * j) 8 = (x >>> (8 * (3 - j))).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h4 := Proof.Seed.getLsbD_append4 (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8)
    (x.extractLsb' 24 8) hi
  have e : ((byteRev32 x).extractLsb' (8 * j) 8).getLsbD i = (byteRev32 x).getLsbD (8 * j + i) := by
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [e]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  unfold byteRev32
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega_arith) with rfl | rfl | rfl | rfl
  · rw [h4.1]; simp [hi]
  · rw [h4.2.1]; simp [hi]
  · rw [h4.2.2.1]; simp [hi]
  · rw [h4.2.2.2]; simp [hi]

/-- Word `w` of block `b` of the tail buffer, as a slot. -/
theorem tail_word {s : State} (h : Room s) {b w : Nat} (hb : b < 8) (hw : w < 4) :
    State.addr (s.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * b) + BitVec.ofNat 64 (4 * w) =
      slotA s (tailAt b w) := by
  have hf := h.fit; rw [slots_eq] at hf
  rw [slotA, slot_addr (by simp [tailAt, tailSlot]; omega_arith), Offset.add_add]
  congr 2; simp [tailAt]; omega_arith

theorem crypt8_wp {s₀ : State} (h : Room s₀) :
    WP isa crypt8 s₀ fun s' =>
      (∀ b < 8, tailBlock s' b = Spec.Seed.crypt (tableKeys s₀) (tailBlock s₀ b)) ∧
      Room s' ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧ s'.gpr sb = s₀.gpr sb ∧
      (∀ j, tableSlot ≤ j → j < slots → slotW s' j = slotW s₀ j) ∧
      Frame [⟨State.addr (s₀.gpr sb), 4 * tableSlot⟩] s₀.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := toArr_ok h
  have sb₁ : s₁.gpr sb = s₀.gpr sb := g₁ _ (by decide)
  have h₁ : Room s₁ := h.congr sb₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (rounds_wp h₁) fun s₂ ⟨q₂, h₂, rd₂, wr₂, sp₂, sb₂, sl₂, f₂⟩ => ?_)
  obtain ⟨s₃, e₃, v₃, o₃, g₃, rd₃, wr₃, sp₃, f₃⟩ := fromArr_ok h₂
  refine WP.of_runBlock ⟨s₃, e₃, ?_⟩
  have sb₃ : s₃.gpr sb = s₀.gpr sb := by rw [g₃ _ (by decide), sb₂, sb₁]
  have hfit := h.fit
  rw [slots_eq] at hfit
  have hkeys : ∀ j < 16, tableKeys s₀ j = tableKeys s₁ j := by
    intro j hj
    simp only [tableKeys]
    rw [o₁ _ (by rw [slots_eq]; simp [tableSlot]; omega_arith) (by simp [tailSlot, tableSlot]; omega_arith),
      o₁ _ (by rw [slots_eq]; simp [tableSlot]; omega_arith) (by simp [tailSlot, tableSlot]; omega_arith)]
  -- The blocks, in the arrays.
  have hin : ∀ b < 8, decodeQ (tailBlock s₀ b) = quadAt s₁ (arrSlot 0) (arrSlot 2) b := by
    intro b hb
    rw [decodeQ_blockAt]
    simp only [quadAt]
    rw [show arrSlot 0 + 8 = arrSlot 1 from rfl, show arrSlot 2 + 8 = arrSlot 3 from rfl,
      v₁ 0 (by decide) b hb, v₁ 1 (by decide) b hb, v₁ 2 (by decide) b hb, v₁ 3 (by decide) b hb,
      show (0 : Nat) = 4 * 0 from rfl, show (4 : Nat) = 4 * 1 from rfl, show (8 : Nat) = 4 * 2 from rfl,
      show (12 : Nat) = 4 * 3 from rfl, tail_word h hb (by decide), tail_word h hb (by decide),
      tail_word h hb (by decide), tail_word h hb (by decide)]
    rfl
  refine ⟨fun b hb => ?_, h₂.congr (by rw [g₃ _ (by decide)]) wr₃, by rw [rd₃, rd₂, rd₁],
    by rw [wr₃, wr₂, wr₁], by rw [sp₃, sp₂, sp₁], sb₃, fun j hj1 hj2 => ?_, ?_⟩
  · rw [crypt_eq, hin b hb, roundsN_congr 16 _ hkeys, ← q₂ b hb]
    apply Vector.ext
    intro i hi
    have h₃ : Room s₃ := h₂.congr (by rw [g₃ _ (by decide)]) wr₃
    simp only [Spec.Seed.blockAt, Vector.getElem_ofFn, encodeSwapped]
    rw [sb₃, ← sb₁, ← sb₂, show BitVec.ofNat 64 i = BitVec.ofNat 64 (4 * (i / 4)) + BitVec.ofNat 64 (i % 4) by
        rw [BitVec.ofNat_add_ofNat]; congr 1; omega_arith,
      ← BitVec.add_assoc, Mem.readW_byte s₃.mem _ (Nat.mod_lt i (by decide))]
    rw [← g₃ sb (by decide), tail_word h₃ hb (by omega_arith), ← slotW, v₃ _ (by omega_arith) b hb,
      byteRev32_byte _ (Nat.mod_lt _ (by decide))]
    congr 2
    simp only [quadAt]
    rcases (show i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3 by omega_arith) with e | e | e | e <;>
      rw [e] <;> rfl
  · rw [o₃ j hj2 hj1, sl₂ j (by simp [tableSlot, tailSlot] at hj1 ⊢; omega_arith) hj2,
      o₁ j hj2 (by simp [tableSlot, tailSlot] at hj1 ⊢; omega_arith)]
  · refine (f₁.trans (by simpa [workR, sb₁] using f₂)).sub (fun r hr => ?_) |>.trans
      (by simpa [sb₂, sb₁] using f₃)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by simp [tailSlot, tableSlot])⟩

end VG.Proof.Seed.Arm

end

end

/-!
# Slots, copies of blocks, and saving registers, on ARMv7

As for SM4 on ARMv7 (`Proof/Sm4/Arm/Copy.lean`, `Prologue.lean`): loads and
stores of the scratch buffer's slots through a base register (`ldW_ok`,
`stW_ok`, and lists of them); `copyBlocks_wp`, the loop copying `c ≥ 1`
blocks of 16 bytes from `r0` to `r12`; the prologue and epilogue's saving
and restoring of the callee-saved registers (`save_ok`, `restore_ok`) in
the slots from `savedSlot`; and the data loop's invariant (`DInv`).
-/

@[expose] public section

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Seed.Arm
open VG.Impl.Aes.Arm (sb t0 t1 kp)

theorem savedSlot_eq : savedSlot = 176 := rfl
theorem ptrSlot_eq : ptrSlot = 185 := rfl
theorem cntSlot_eq : cntSlot = 186 := rfl
theorem tableSlot_eq : tableSlot = 144 := rfl
theorem tableEnd_eq : tableEnd = 176 := rfl
theorem tailSlot_eq : tailSlot = 112 := rfl

/-! ## Addresses and memory -/

theorem off_sub_toNat (B : Addr) {t e : Nat} (h : e ≤ t) (ht : t < 2 ^ 64) :
    (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat = t - e := by
  rw [Offset.add_sub_add _ h, BitVec.toNat_ofNat]; omega_arith

theorem off_sub_not (B : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat < n := by
  rw [Offset.add_sub_add_left]; exact Offset.not_lt_sub_ofNat h ht hn he

theorem not_contains_off (b : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (⟨b + BitVec.ofNat 64 e, n⟩ : Region).Contains (b + BitVec.ofNat 64 t) 1 := by
  simp only [Region.Contains]; intro hc; exact off_sub_not b h ht hn he (by omega_arith)

/-- A byte of a little-endian 32-bit word stored from a load. -/
theorem writeW_readW32_apply (m m' : Mem) (a c x : Addr) :
    m.writeW a (m'.readW c 32) x =
      if (x - a).toNat < 4 then m' (c + BitVec.ofNat 64 (x - a).toNat) else m x := by
  simp only [Mem.writeW, Mem.write, Mem.readW, BitVec.setWidth_eq]
  split
  · rename_i h
    exact Mem.extractLsb'_read m' c (n := 4) h
  · rfl

/-- Slot `k` is in the scratch buffer. -/
theorem slot_inR {rs : List Region} {b : BitVec 32} {n k : Nat} (hr : (⟨State.addr b, 4 * n⟩ : Region) ∈ rs)
    (hfit : b.toNat + 4 * n ≤ 2 ^ 32) (hk : k < n) : InRegions rs (wordAddr b k) 4 :=
  ⟨_, hr, by
    rw [slot_addr (by omega_arith)]
    have := toNat_addr b
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- `subs d, n, #1`. -/
theorem subs1_ok (s : State) (d : Reg) :
    ∃ s', runBlock isa [.subs d d (.imm 1)] s = some s' ∧ s'.gpr d = s.gpr d - 1 ∧ s'.z = (s.gpr d - 1 == 0) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨(subFlags s (s.gpr d) 1).setReg d (s.gpr d - 1), ?_, RegUpd.gpr_setReg_self _ _ _, by rw [RegUpd.z_setReg]; rfl,
    fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr]; rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.subs d d (.imm 1)) s = some ((subFlags s (s.gpr d) 1).setReg d (s.gpr d - 1)) by
    simp [exec, Op2.eval]; decide, runStep_some, runBlock_nil]

theorem ofNat32_beq_zero {x : Nat} (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

/-- `mov d, #v` (`v` encodable). -/
theorem movImm_ok (s : State) (d : Reg) (v : BitVec 32) (hv : encodable v = true) :
    ∃ s', runBlock isa [.mov d (.imm v)] s = some s' ∧ s'.gpr d = v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d v, by
    rw [runBlock_cons, show exec (.mov d (.imm v)) s = some (s.setReg d v) by simp [exec, Op2.eval, hv],
      runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-! ## Copying blocks -/

/-- What a copy keeps, after its first `k` bytes. -/
structure Copied (A B : Addr) (c : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  copied : ∀ t < k, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem

/-- `ldr t0, [r0, #d]; str t0, [r1, #d]`: the copy's next word. -/
theorem copyWord_ok {A B : BitVec 32} {c : Nat} {s₀ s : State} {j d : Nat} (hd : d < 16) (hd4 : d % 4 = 0)
    (hj : j < c) (hfA : A.toNat + 16 * c ≤ 2 ^ 32) (hfB : B.toNat + 16 * c ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr B, 16 * c⟩)
    (hr : InRegions (s.rd ++ s.wr) (State.addr A + BitVec.ofNat 64 (16 * j + d)) 4)
    (hw : InRegions s.wr (State.addr B + BitVec.ofNat 64 (16 * j + d)) 4)
    (h0 : s.gpr .r0 = A + BitVec.ofNat 32 (16 * j)) (h1 : s.gpr .r12 = B + BitVec.ofNat 32 (16 * j))
    (hi : Copied (State.addr A) (State.addr B) c s₀ (16 * j + d) s) :
    ∃ s', runBlock isa [.ldr t0 .r0 d, .str t0 .r12 d] s = some s' ∧
      Copied (State.addr A) (State.addr B) c s₀ (16 * j + d + 4) s' ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have eA : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = State.addr A + BitVec.ofNat 64 (16 * j + d) := by
    rw [h0, add_ofNat_ofNat, addr_add (by omega_arith)]
  have eB : State.addr (s.gpr .r12 + BitVec.ofNat 32 d) = State.addr B + BitVec.ofNat 64 (16 * j + d) := by
    rw [h1, add_ofNat_ofNat, addr_add (by omega_arith)]
  have h₁ : (s.setReg t0 (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32)).gpr .r12 = s.gpr .r12 :=
    RegUpd.gpr_setReg_of_ne _ _ (by decide)
  refine ⟨{ s.setReg t0 (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32) with
      mem := s.mem.writeW (State.addr B + BitVec.ofNat 64 (16 * j + d))
        (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32) }, ?_,
    ⟨fun t ht' => ?_, hi.frame.trans fun x hx => ?_⟩, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩
  · rw [runBlock_cons, exec_ldr (by omega_arith) (by rw [eA]; exact hr), eA, runStep_some, runBlock_cons,
      exec_str (by omega_arith) (by rw [h₁, eB]; exact hw), runStep_some, runBlock_nil, h₁, eB,
      RegUpd.gpr_setReg_self]
    rfl
  · have hn : 16 * c < 2 ^ 64 := by omega_arith
    have hAs : ∀ t < 16 * c, s.mem (State.addr A + BitVec.ofNat 64 t) = s₀.mem (State.addr A + BitVec.ofNat 64 t) :=
      fun t ht => hi.frame.bytes (R := ⟨State.addr A, 16 * c⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep) (by simp only; omega_arith) ht
    show (s.mem.writeW _ _) _ = _
    rw [writeW_readW32_apply]
    by_cases h8 : 16 * j + d ≤ t
    · rw [ite_eq_left (by rw [off_sub_toNat _ h8 (by omega_arith)]; omega_arith), off_sub_toNat _ h8 (by omega_arith),
        Offset.add_add, show 16 * j + d + (t - (16 * j + d)) = t by omega_arith, hAs t (by omega_arith)]
    · rw [ite_eq_right (off_sub_not _ (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))]
      exact hi.copied t (by omega_arith)
  · show (s.mem.writeW _ _) x = s.mem x
    rw [writeW_readW32_apply, ite_eq_right fun h =>
      hx _ (List.mem_singleton_self _) (Offset.sub_base _ (show 16 * j + d + 4 ≤ 16 * c by omega_arith) _
        (by simp only [Region.Contains]; omega_arith))]

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : BitVec 32) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  src : s.gpr .r0 = A + BitVec.ofNat 32 (16 * j)
  dst : s.gpr .r12 = B + BitVec.ofNat 32 (16 * j)
  cnt : s.gpr .r3 = BitVec.ofNat 32 (c - j)
  cp : Copied (State.addr A) (State.addr B) c s₀ (16 * j) s
  regs : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem copyBlocks_wp {A B : BitVec 32} {c : Nat} {s₀ : State} (hc : 0 < c) (hc8 : c ≤ 8)
    (hfA : A.toNat + 16 * c ≤ 2 ^ 32) (hfB : B.toNat + 16 * c ≤ 2 ^ 32)
    (hA : ∀ t < 16 * c, t % 4 = 0 → InRegions (s₀.rd ++ s₀.wr) (State.addr A + BitVec.ofNat 64 t) 4)
    (hB : ∀ t < 16 * c, t % 4 = 0 → InRegions s₀.wr (State.addr B + BitVec.ofNat 64 t) 4)
    (hsep : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega_arith, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  have rA : ∀ d < 16, d % 4 = 0 → ∀ s : State, s.rd = s₀.rd → s.wr = s₀.wr →
      InRegions (s.rd ++ s.wr) (State.addr A + BitVec.ofNat 64 (16 * j + d)) 4 := fun d hd hd4 s h1 h2 => by
    rw [h1, h2]; exact hA _ (by omega_arith) (by omega_arith)
  have rB : ∀ d < 16, d % 4 = 0 → ∀ s : State, s.wr = s₀.wr →
      InRegions s.wr (State.addr B + BitVec.ofNat 64 (16 * j + d)) 4 := fun d hd hd4 s h2 => by
    rw [h2]; exact hB _ (by omega_arith) (by omega_arith)
  obtain ⟨s₁, e₁, c₁, g₁, rd₁, wr₁, sp₁⟩ := copyWord_ok (d := 0) (by decide) (by decide) hj hfA hfB hsep
    (rA 0 (by decide) (by decide) s hi.rd hi.wr) (rB 0 (by decide) (by decide) s hi.wr) hi.src hi.dst
    (by simpa using hi.cp)
  obtain ⟨s₂, e₂, c₂, g₂, rd₂, wr₂, sp₂⟩ := copyWord_ok (d := 4) (by decide) (by decide) hj hfA hfB hsep
    (rA 4 (by decide) (by decide) s₁ (rd₁.trans hi.rd) (wr₁.trans hi.wr))
    (rB 4 (by decide) (by decide) s₁ (wr₁.trans hi.wr))
    (by rw [g₁ _ (by decide), hi.src]) (by rw [g₁ _ (by decide), hi.dst]) (by simpa using c₁)
  obtain ⟨s₃, e₃, c₃, g₃, rd₃, wr₃, sp₃⟩ := copyWord_ok (d := 8) (by decide) (by decide) hj hfA hfB hsep
    (rA 8 (by decide) (by decide) s₂ (rd₂.trans (rd₁.trans hi.rd)) (wr₂.trans (wr₁.trans hi.wr)))
    (rB 8 (by decide) (by decide) s₂ (wr₂.trans (wr₁.trans hi.wr)))
    (by rw [g₂ _ (by decide), g₁ _ (by decide), hi.src]) (by rw [g₂ _ (by decide), g₁ _ (by decide), hi.dst])
    c₂
  obtain ⟨s₄, e₄, c₄, g₄, rd₄, wr₄, sp₄⟩ := copyWord_ok (d := 12) (by decide) (by decide) hj hfA hfB hsep
    (rA 12 (by decide) (by decide) s₃ (rd₃.trans (rd₂.trans (rd₁.trans hi.rd)))
      (wr₃.trans (wr₂.trans (wr₁.trans hi.wr))))
    (rB 12 (by decide) (by decide) s₃ (wr₃.trans (wr₂.trans (wr₁.trans hi.wr))))
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.src])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.dst]) c₃
  have g₄' : ∀ r, r ≠ t0 → s₄.gpr r = s.gpr r := fun r hr => by rw [g₄ r hr, g₃ r hr, g₂ r hr, g₁ r hr]
  obtain ⟨s₅, e₅, a₅, o₅, m₅, rd₅, wr₅, sp₅⟩ := addImm_ok s₄ .r0 .r0 16 (by decide)
  obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := addImm_ok s₅ .r12 .r12 16 (by decide)
  obtain ⟨s₇, e₇, c₇, z₇, o₇, m₇, rd₇, wr₇, sp₇⟩ := subs1_ok s₆ .r3
  refine WP.of_runBlock ⟨s₇, by
    rw [show ([Instr.ldr t0 .r0 0, .str t0 .r12 0, .ldr t0 .r0 4, .str t0 .r12 4,
      .ldr t0 .r0 8, .str t0 .r12 8, .ldr t0 .r0 12, .str t0 .r12 12,
      .dp .add .r0 .r0 (.imm 16), .dp .add .r12 .r12 (.imm 16), .subs .r3 .r3 (.imm 1)] : List Instr) =
      [.ldr t0 .r0 0, .str t0 .r12 0] ++ ([.ldr t0 .r0 4, .str t0 .r12 4] ++ ([.ldr t0 .r0 8, .str t0 .r12 8] ++
      ([.ldr t0 .r0 12, .str t0 .r12 12] ++ ([.dp .add .r0 .r0 (.imm 16)] ++
      ([.dp .add .r12 .r12 (.imm 16)] ++ [.subs .r3 .r3 (.imm 1)]))))) from rfl,
      runBlock_append, e₁, Option.bind_some, runBlock_append, e₂, Option.bind_some, runBlock_append, e₃,
      Option.bind_some, runBlock_append, e₄, Option.bind_some, runBlock_append, e₅, Option.bind_some,
      runBlock_append, e₆, Option.bind_some, e₇], ?_⟩
  have hc₇ : s₇.gpr .r3 = BitVec.ofNat 32 (c - (j + 1)) := by
    rw [c₇, o₆ _ (by decide), o₅ _ (by decide), g₄' _ (by decide), hi.cnt,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith),
      show c - j - 1 = c - (j + 1) by omega_arith]
  have hm : s₇.mem = s₄.mem := by rw [m₇, m₆, m₅]
  have hinv : CopyInv A B c s₀ (j + 1) s₇ := by
    refine ⟨?_, ?_, hc₇, ⟨fun t ht => ?_, by rw [hm]; exact c₄.frame⟩, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr],
      by rw [sp₇, sp₆, sp₅, sp₄, sp₃, sp₂, sp₁, hi.sp]⟩
    · rw [o₇ _ (by decide), o₆ _ (by decide), a₅, g₄' _ (by decide), hi.src,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_ofNat,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [o₇ _ (by decide), a₆, o₅ _ (by decide), g₄' _ (by decide), hi.dst,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_ofNat,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [hm]; exact c₄.copied t (by omega_arith)
    · rw [o₇ r h3, o₆ r h2, o₅ r h1, g₄' r h4, hi.regs r h1 h2 h3 h4]
  have hz : s₇.z = decide (c - (j + 1) = 0) := by
    rw [z₇, ← c₇, hc₇, ofNat32_beq_zero (by omega_arith)]
  by_cases hl : j + 1 = c
  · refine .inl ⟨(eval_ne s₇).trans (by rw [hz]; simp; omega_arith),
      by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_ne s₇).trans (by rw [hz]; simp; omega_arith), c - (j + 1), by omega_arith, j + 1, rfl,
      by omega_arith, hinv⟩

/-! ## Slots -/

/-- The scratch buffer at `b`, in the writable regions. -/
structure ScrIn (rs : List Region) (b : BitVec 32) : Prop where
  mem : (⟨State.addr b, 4 * slots⟩ : Region) ∈ rs
  fit : b.toNat + 4 * slots ≤ 2 ^ 32

theorem ScrIn.slot {rs : List Region} {b : BitVec 32} (h : ScrIn rs b) {k : Nat} (hk : k < slots) :
    InRegions rs (wordAddr b k) 4 := slot_inR h.mem h.fit hk

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A slot is inside the scratch buffer. -/
theorem slot_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {k : Nat} (hk : k < slots) :
    Region.Sub ⟨wordAddr b k, 4⟩ ⟨State.addr b, 4 * slots⟩ := by
  rw [slot_addr (by omega_arith)]
  exact Offset.sub_base _ (by omega_arith)

/-- A slot after a store to a slot. -/
theorem readW_slot_write {m : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {j k : Nat}
    (v : BitVec 32) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 32 = if j = k then v else m.readW (wordAddr b j) 32 := by
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self32 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega_arith) (by omega_arith) h) (by decide)

/-- `ldr d, [n, #4 k]`, `n` holding `b`. -/
theorem ldW_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : 4 * k < 4096)
    (hin : InRegions (s.rd ++ s.wr) (wordAddr b k) 4) :
    ∃ s', runBlock isa [.ldr d n (4 * k)] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d (s.mem.readW (wordAddr b k) 32), by
    rw [runBlock_cons, exec_ldr hk (by rw [hn]; exact hin), hn, runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-- `str t, [n, #4 k]`, `n` holding `b`. -/
theorem stW_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : 4 * k < 4096)
    (hin : InRegions s.wr (wordAddr b k) 4) :
    runBlock isa [.str t n (4 * k)] s = some { s with mem := s.mem.writeW (wordAddr b k) (s.gpr t) } := by
  rw [runBlock_cons, exec_str hk (by rw [hn]; exact hin), hn, runStep_some, runBlock_nil]

/-- A store to a slot of the scratch buffer. -/
theorem stSlot_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.str t n (4 * k)] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr t) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.z = s.z ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem :=
  ⟨_, stW_ok s t n hn (by rw [slots_eq] at hk; omega_arith) (hw.slot hk), rfl, rfl, rfl, rfl, rfl, rfl,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)⟩

/-- A load of a slot of the scratch buffer. -/
theorem ldSlot_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.ldr d n (4 * k)] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ldW_ok s d n hn (by rw [slots_eq] at hk; omega_arith) (inRd (hw.slot hk))

/-- Stores of registers to distinct slots, through `n`, which none of them is. -/
theorem stW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Nat × Reg)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < slots) →
    ∃ s', runBlock isa (L.map fun x => .str x.2 n (4 * x.1)) s = some s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem ∧
      (∀ k, k ∉ L.map (·.1) → k < slots → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      ∀ x ∈ L, s'.mem.readW (wordAddr b x.1) 32 = s.gpr x.2
  | [], s, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hnd, hin => by
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, sp₁, -, f₁⟩ := stSlot_ok s x.2 n hn (hin x List.mem_cons_self) hw
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', g', rd', wr', sp', f', o', v'⟩ :=
      stW_list_ok n L s₁ (by rw [g₁, hn]) (by rw [wr₁]; exact hw) hnd.2
        fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁, sp'.trans sp₁,
      (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hw.fit (hin x List.mem_cons_self)⟩).trans f',
      fun k hk hks => ?_,
      fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_append, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hk
      rw [o' k hk.2 hks, m₁, readW_slot_write hw.fit _ hks (hin x List.mem_cons_self)]
      simp only [hk.1, ite_false]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1 (hin _ List.mem_cons_self), m₁, Mem.readW_writeW_self32]
      · rw [v' y hy, g₁]

/-- Loads of distinct slots into distinct registers, through `n`, which none of them is. -/
theorem ldW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Reg × Nat)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (∀ x ∈ L, x.1 ≠ n) → (L.map (·.1)).Nodup → (∀ x ∈ L, x.2 < slots) →
    ∃ s', runBlock isa (L.map fun x => .ldr x.1 n (4 * x.2)) s = some s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ L.map (·.1) → s'.gpr r = s.gpr r) ∧
      ∀ x ∈ L, s'.gpr x.1 = s.mem.readW (wordAddr b x.2) 32
  | [], s, _, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hne, hnd, hin => by
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s x.1 n hn (hin x List.mem_cons_self) hw
    have hn₁ : s₁.gpr n = b := by rw [o₁ _ (hne x List.mem_cons_self).symm, hn]
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', m', rd', wr', sp', o', v'⟩ := ldW_list_ok n L s₁ hn₁ (by rw [wr₁]; exact hw)
      (fun y hy => hne y (List.mem_cons_of_mem _ hy)) hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, m'.trans m₁, rd'.trans rd₁, wr'.trans wr₁, sp'.trans sp₁, fun r hr => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_append, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o' r hr.2, o₁ r hr.1]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1, v₁]
      · rw [v' y hy, m₁]

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers, in the order of `savedRegs`. -/
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1))[i]?).getD .r4

theorem savedRegs_eq : savedRegs = (List.range 9).map fun i => (sreg i, savedSlot + i) := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : BitVec 32) (m : Mem) : Prop :=
  ∀ i < 9, m.readW (wordAddr b (savedSlot + i)) 32 = s₀.gpr (sreg i)

theorem save_ok {s : State} {base : Reg} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr base = b) :
    ∃ s', runBlock isa (saveRegs base) s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem ∧
      ∀ k, k < savedSlot → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32 := by
  let L : List (Nat × Reg) := (List.range 9).map fun i => (savedSlot + i, sreg i)
  have hL : saveRegs base = L.map fun x => .str x.2 base (4 * x.1) := by
    rw [saveRegs, savedRegs_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 9).map fun i => savedSlot + i := by
    simp only [L, List.map_map]; rfl
  obtain ⟨s', e', g', rd', wr', sp', f', o', v'⟩ := stW_list_ok base L s hb hw (by rw [hslots]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [savedSlot_eq, slots_eq]; omega_arith)
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, g', rd', wr', sp', f', fun k hk => o' k ?_ (by
    rw [savedSlot_eq] at hk; rw [slots_eq]; omega_arith)⟩
  · exact v' (savedSlot + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
  · rw [hslots]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i hi h; omega_arith

theorem sreg_ne_r12 : ∀ i < 9, sreg i ≠ .r12 := by decide

theorem restore_ok {s₀ s : State} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr .r12 = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa (restoreRegs .r12) s = some s' ∧ (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 9, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let L : List (Reg × Nat) := (List.range 9).map fun i => (sreg i, savedSlot + i)
  have hL : restoreRegs .r12 = L.map fun x => .ldr x.1 .r12 (4 * x.2) := by
    rw [restoreRegs, savedRegs_eq]
  have hregs : L.map (·.1) = (List.range 9).map sreg := by simp only [L, List.map_map]; rfl
  obtain ⟨s', e', m', rd', wr', sp', o', v'⟩ := ldW_list_ok .r12 L s hb hw
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx; exact sreg_ne_r12 i hi)
    (by rw [hregs]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [savedSlot_eq, slots_eq]; omega_arith)
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, fun r hr => o' r ?_, m', rd', wr', sp'⟩
  · rw [v' (sreg i, savedSlot + i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)]
    exact hs i hi
  · rw [hregs]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    exact fun i hi h => hr i hi h.symm

/-! ## The data -/

/-- The first `k` blocks are `F`'s, the others still `m₀`'s. -/
def DInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Seed.Block) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 16 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

theorem blocksAt_of_dinv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Seed.Block}
    (h : DInv m₀ m D n n F) : Spec.Seed.blocksAt m D n = (List.range n).map F := by
  simp only [Spec.Seed.blocksAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext; intro t ht
  simp only [Spec.Seed.blockAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_left (by omega_arith), show (16 * j + t) / 16 = j by omega_arith,
    show (16 * j + t) % 16 = t by omega_arith]
  simp [Vector.getD, ht]

end VG.Proof.Seed.Arm

end

end

/-!
# A group of blocks of SEED ECB on ARMv7

`dataGroup_wp`: one iteration of the data loop copies the group's blocks
(eight, or the last one to seven) to the tail buffer, transforms it
(`crypt8_wp`), copies the blocks back and steps to the next group. The data
pointer and the blocks left live in their slots (`ptrSlot`, `cntSlot`) between
the steps, which use every other register.
-/

@[expose] public section

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Seed.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR lsrOp ldS stS)

/-! ## Small blocks -/

theorem lsr3_beq {v : Nat} (hv : v < 2 ^ 32) :
    (BitVec.ofNat 32 v >>> 3 - 0 == 0) = decide (v < 8) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

theorem movR_ok (s : State) (d n : Reg) :
    ∃ s', runBlock isa [movR d n] s = some s' ∧ s'.gpr d = s.gpr n ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d (s.gpr n), by
    rw [runBlock_cons, show exec (movR d n) s = some (s.setReg d (s.gpr n)) by simp [movR, exec, Op2.eval],
      runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-- `r3 := min(r2, 8)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hn : s.gpr .r2 = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    WP isa groupCount s fun s' => s'.gpr .r3 = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .r3 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₂ := s.setReg t0 (s.gpr .r2 >>> 3)
  let s₃ := subFlags s₂ (s₂.gpr t0) 0
  obtain e₂₃ : runBlock isa [.mov t0 (lsrOp .r2 3), .cmp t0 (.imm 0)] s = some s₃ := by
    rw [runBlock_cons, show exec (.mov t0 (lsrOp .r2 3)) s = some s₂ by simp [exec, Op2.eval, lsrOp, s₂],
      runStep_some, runBlock_cons,
      show exec (.cmp t0 (.imm 0)) s₂ = some s₃ by simp [exec, Op2.eval, s₃]; decide,
      runStep_some, runBlock_nil]
  obtain z₃ : s₃.z = (BitVec.ofNat 32 v >>> 3 - 0 == 0) := by
    show (s₂.gpr t0 - 0 == 0) = _; rw [RegUpd.gpr_setReg_self, hn]
  obtain o₃ : ∀ r, r ≠ t0 → s₃.gpr r = s.gpr r := fun r hr => by
    show s₂.gpr r = _; rw [RegUpd.gpr_setReg_of_ne _ _ hr]
  obtain r2₃ : s₃.gpr .r2 = BitVec.ofNat 32 v := by rw [o₃ _ (by decide), hn]
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₃, e₂₃, ?_⟩)
  refine WP.ite (decide (8 ≤ v)) ((eval_ne s₃).trans (by
      rw [z₃, lsr3_beq hv]; by_cases h : v < 8 <;> simp [h] <;> omega_arith)) (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movImm_ok s₃ .r3 8 (by decide)
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 h2 => by rw [o₄ r h1, o₃ r h2], m₄, rd₄, wr₄, sp₄⟩
    rw [r₄, Nat.min_eq_right (by simp at h; omega_arith)]; rfl
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movR_ok s₃ .r3 .r2
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 h2 => by rw [o₄ r h1, o₃ r h2], m₄, rd₄, wr₄, sp₄⟩
    rw [r₄, r2₃, Nat.min_eq_left (by simp at h; omega_arith)]

/-- `subs d, n, m`. -/
theorem subsR_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [.subs d n (.reg m)] s = some s' ∧ s'.gpr d = s.gpr n - s.gpr m ∧
      s'.z = (s.gpr n - s.gpr m == 0) ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨(subFlags s (s.gpr n) (s.gpr m)).setReg d (s.gpr n - s.gpr m), ?_, RegUpd.gpr_setReg_self _ _ _,
    by rw [RegUpd.z_setReg]; rfl, fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr]; rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.subs d n (.reg m)) s =
    some ((subFlags s (s.gpr n) (s.gpr m)).setReg d (s.gpr n - s.gpr m)) by simp [exec, Op2.eval],
    runStep_some, runBlock_nil]

theorem toNat_add32 (D : BitVec 32) {d : Nat} (h : D.toNat + d < 2 ^ 32) :
    (D + BitVec.ofNat 32 d).toNat = D.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : d < 2 ^ 32), Nat.mod_eq_of_lt h]

/-! ## The scratch buffer's contents -/

/-- The slots `lo … hi - 1` of the scratch buffer at `b`. -/
abbrev slotsRegion (b : BitVec 32) (lo hi : Nat) : Region :=
  ⟨State.addr b + BitVec.ofNat 64 (4 * lo), 4 * (hi - lo)⟩

/-- A slot outside a frame. -/
theorem slot_keep {rs : List Region} {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {lo hi : Nat} (hhi : hi ≤ slots) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b lo hi).Disjoint r)
    {k : Nat} (hk1 : lo ≤ k) (hk2 : k < hi) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  rw [slots_eq] at hfit hhi
  rw [slot_addr (by omega_arith)]
  exact hf.readW (VG.Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)) hd (by decide)

/-- What the data loop keeps in the scratch buffer: the table and the saved
registers, in the slots from `tableSlot` to `ptrSlot`. -/
structure ScrOk (s₀ : State) (b : BitVec 32) (E : Nat → Spec.Seed.Word) (m : Mem) : Prop where
  keys : ∀ e < 32, m.readW (wordAddr b (tableSlot + e)) 32 = E e
  saved : Saved s₀ b m

theorem ScrOk.frame {s₀ : State} {b : BitVec 32} {E : Nat → Spec.Seed.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b tableSlot ptrSlot).Disjoint r) : ScrOk s₀ b E m' := by
  refine ⟨fun e he => ?_, fun i hi => ?_⟩
  · rw [← h.keys e he]
    exact slot_keep hfit (by decide) hf hd (by omega_arith) (by rw [ptrSlot_eq, tableSlot_eq]; omega_arith)
  · rw [← h.saved i hi]
    exact slot_keep hfit (by decide) hf hd (by rw [savedSlot_eq, tableSlot_eq]; omega_arith)
      (by rw [savedSlot_eq, ptrSlot_eq]; omega_arith)

/-! ## The data loop -/

/-- Round `j + 1`'s key, from the table's words `E`. -/
def keyPairs (E : Nat → Spec.Seed.Word) (j : Nat) : Spec.Seed.Word × Spec.Seed.Word := (E (2 * j), E (2 * j + 1))

/-- Each block, transformed: `crypt` with the table's round keys `E`. -/
def outF (m₀ : Mem) (D : Addr) (E : Nat → Spec.Seed.Word) (j : Nat) : Spec.Seed.Block :=
  Spec.Seed.crypt (keyPairs E) (Spec.Seed.blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))

theorem blockAt_getD (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    (Spec.Seed.blockAt m p).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Seed.blockAt, Vector.getD, hi]

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : BitVec 32) (n : Nat) : Prop where
  scr : ScrIn s₀.wr b
  dat : (⟨State.addr D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr b, 4 * slots⟩
  fitD : D.toNat + 16 * n ≤ 2 ^ 32

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Seed.Word) (k : Nat) (s : State) :
    Prop where
  base : s.gpr sb = b
  dp : s.gpr .r1 = D + BitVec.ofNat 32 (128 * k)
  np : s.gpr .r2 = BitVec.ofNat 32 (n - 8 * k)
  lt : 8 * k < n
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (State.addr D) n (8 * k) (outF s₀.mem (State.addr D) E)
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Seed.Word) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (State.addr D) n n (outF s₀.mem (State.addr D) E)
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem dataGroup_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {E : Nat → Spec.Seed.Word} (hp : GPre s₀ b D n)
    {k : Nat} {s : State} (hi : GInv s₀ b D n E k s) :
    WP isa group s fun s' => (s'.z = true ∧ GDone s₀ b D n E s') ∨
      (s'.z = false ∧ GInv s₀ b D n E (k + 1) s') := by
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain hb := toNat_addr b
  rw [slots_eq] at hfit
  obtain hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega_arith
  let v := n - 8 * k
  let c := min v 8
  obtain hv : v < 2 ^ 32 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc8 : c ≤ 8 := by omega_arith
  obtain hkc : 128 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 32 (128 * k)
  let T := b + BitVec.ofNat 32 (4 * tailSlot)
  obtain hA : State.addr A = State.addr D + BitVec.ofNat 64 (128 * k) := addr_add (by omega_arith)
  obtain hT : State.addr T = State.addr b + BitVec.ofNat 64 (4 * tailSlot) := addr_add (by rw [tailSlot_eq]; omega_arith)
  obtain hAn : A.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by omega_arith)]; omega_arith
  obtain hTn : T.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by rw [tailSlot_eq]; omega_arith), tailSlot_eq]; omega_arith
  obtain hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  obtain hwD : (⟨State.addr D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain inT : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (State.addr T + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwS.mem, ?_⟩
    rw [hT, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by rw [slots_eq, tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain inA : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (State.addr A + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwD, ?_⟩
    rw [hA, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain subA : Region.Sub ⟨State.addr A, 16 * c⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [hA]; exact VG.Offset.sub_base _ (by omega_arith)
  obtain subT : Region.Sub ⟨State.addr T, 16 * c⟩ ⟨State.addr b, 4 * slots⟩ := by
    rw [hT]; exact VG.Offset.sub_base _ (by rw [slots_eq, tailSlot_eq]; omega_arith)
  obtain sepAT : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr T, 16 * c⟩ :=
    (hp.sep.sub_left subA).sub_right subT
  -- The regions the steps write keep the slots from `tableSlot`.
  obtain dT : (slotsRegion b tableSlot slots).Disjoint ⟨State.addr T, 16 * c⟩ := by
    rw [hT]; exact VG.Offset.disjoint _ (by rw [tableSlot_eq, tailSlot_eq]; omega_arith)
      (by rw [tableSlot_eq, slots_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain dA : (slotsRegion b tableSlot slots).Disjoint ⟨State.addr A, 16 * c⟩ :=
    ((hp.sep.sub_left subA).sub_right (VG.Offset.sub_base _ (by rw [tableSlot_eq, slots_eq]))).symm
  obtain dTab : (slotsRegion b tableSlot slots).Disjoint ⟨State.addr b, 4 * tableSlot⟩ :=
    VG.Offset.disjoint_base _ (by omega_arith) (by rw [tableSlot_eq, slots_eq]; omega_arith)
  obtain sub_ts : ∀ l u, tableSlot ≤ l → l ≤ u → u ≤ slots →
      (slotsRegion b l u).Sub (slotsRegion b tableSlot slots) :=
    fun l u h1 h2 h3 => VG.Offset.sub _ (by omega_arith) (by rw [slots_eq] at h3 ⊢; omega_arith)
  obtain subTab : (slotsRegion b tableSlot ptrSlot).Sub (slotsRegion b tableSlot slots) :=
    sub_ts _ _ (Nat.le_refl _) (by decide) (by decide)
  obtain dD : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨State.addr b, 4 * slots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨State.addr D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  have r1₀ : s.gpr .r1 = A := hi.dp
  unfold group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.np hv) fun s₁ ⟨r3₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a, sp₂a⟩ := movR_ok s₁ .r0 .r1
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := addImm_ok s₂a .r12 sb (BitVec.ofNat 32 (4 * tailSlot)) (by decide)
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂a, m₁]
  obtain g₂ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₂.gpr r = s.gpr r :=
    fun r h0 h12 h3 h4 => by rw [o₂ r h12, o₂a r h0, o₁ r h3 h4]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show ([movR .r0 .r1, tailAddr .r12] : List Instr) = [movR .r0 .r1] ++ [tailAddr .r12] from rfl,
      runBlock_append, e₂a, Option.bind_some]; exact e₂, ?_⟩)
  refine WP.mono (copyBlocks_wp (A := A) (B := T) hc0 hc8 hAn hTn
    (fun t ht h4 => by rw [rd₂', wr₂']; exact inRd (inA t ht h4))
    (fun t ht h4 => by rw [wr₂']; exact inT t ht h4) sepAT
    ⟨by rw [o₂ _ (by decide), r₂a, o₁ _ (by decide) (by decide), r1₀]; simp [A],
      by rw [r₂, o₂a _ (by decide), o₁ _ (by decide) (by decide), hi.base]; simp [T],
      by rw [o₂ _ (by decide), o₂a _ (by decide), r3₁, Nat.sub_zero], ⟨fun t ht => by omega_arith, Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s₃ h₃ => ?_
  obtain f₃ : Frame [⟨State.addr T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact h₃.cp.frame
  obtain g₃ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₃.gpr r = s.gpr r :=
    fun r h0 h12 h3 h4 => by rw [h₃.regs r h0 h12 h3 h4, g₂ r h0 h12 h3 h4]
  obtain base₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hi.base]
  obtain sc₃ : ScrOk s₀ b E s₃.mem := hi.scr.frame hfit' f₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dT.sub_left subTab
  obtain wr₃ : s₃.wr = s.wr := by rw [h₃.wr, wr₂']
  obtain rd₃ : s₃.rd = s.rd := by rw [h₃.rd, rd₂']
  obtain sp₃ : s₃.sp = s.sp := by rw [h₃.sp, sp₂, sp₂a, sp₁]
  obtain hwS₃ : ScrIn s₃.wr b := by rw [wr₃]; exact hwS
  -- The data pointer and the blocks left to their slots.
  unfold cryptSaved
  obtain ⟨s₄a, e₄a, m₄a, g₄a, rd₄a, wr₄a, sp₄a, -, f₄a⟩ := stSlot_ok s₃ .r1 sb (k := ptrSlot) base₃ (by decide) hwS₃
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, -, f₄⟩ := stSlot_ok s₄a .r2 sb (k := cntSlot) (by rw [g₄a, base₃])
    (by decide) (by rw [wr₄a]; exact hwS₃)
  obtain r1₃ : s₃.gpr .r1 = A := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), r1₀]
  obtain r2₃ : s₃.gpr .r2 = BitVec.ofNat 32 v := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hi.np]
  obtain fs : Frame [⟨wordAddr b ptrSlot, 4⟩, ⟨wordAddr b cntSlot, 4⟩] s₃.mem s₄.mem :=
    (f₄a.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (f₄.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
  obtain hsub : ∀ r ∈ [(⟨wordAddr b ptrSlot, 4⟩ : Region), ⟨wordAddr b cntSlot, 4⟩],
      Region.Sub r ⟨State.addr b, 4 * slots⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact slot_sub hfit' (by decide)
    · exact slot_sub hfit' (by decide)
  obtain dsTab : ∀ r ∈ [(⟨wordAddr b ptrSlot, 4⟩ : Region), ⟨wordAddr b cntSlot, 4⟩],
      (slotsRegion b tableSlot ptrSlot).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [ptrSlot_eq, cntSlot_eq]); omega_arith)] <;>
      exact VG.Offset.disjoint _ (by (try simp only [tableSlot_eq, ptrSlot_eq, cntSlot_eq]); omega_arith)
        (by (try simp only [tableSlot_eq, ptrSlot_eq]); omega_arith) (by (try simp only [ptrSlot_eq, cntSlot_eq]); omega_arith)
  obtain sc₄ : ScrOk s₀ b E s₄.mem := sc₃.frame hfit' fs dsTab
  obtain base₄ : s₄.gpr sb = b := by rw [g₄, g₄a, base₃]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₄a, wr₃]
  obtain dp₄ : s₄.mem.readW (wordAddr b ptrSlot) 32 = A := by
    rw [m₄, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_right (by decide), m₄a,
      readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl, r1₃]
  obtain np₄ : s₄.mem.readW (wordAddr b cntSlot) 32 = BitVec.ofNat 32 v := by
    rw [m₄, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl, g₄a, r2₃]
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show ([stS ptrSlot .r1, stS cntSlot .r2] : List Instr) =
      [.str .r1 sb (4 * ptrSlot)] ++ [.str .r2 sb (4 * cntSlot)] from rfl, runBlock_append, e₄a, Option.bind_some, e₄],
    ?_⟩))
  -- The eight blocks.
  obtain hR₄ : Room s₄ := ⟨by unfold scratchR; rw [base₄, wr₄']; exact hwS.mem, by rw [base₄]; exact hfit'⟩
  refine WP.seq (WP.mono (crypt8_wp hR₄) fun s₅ ⟨b₅, _, rd₅', wr₅', sp₅', sb₅, sl₅, f₅'⟩ => ?_)
  obtain base₅ : s₅.gpr sb = b := by rw [sb₅, base₄]
  obtain f₅ : Frame [⟨State.addr b, 4 * tableSlot⟩] s₄.mem s₅.mem := by rw [base₄] at f₅'; exact f₅'
  obtain keep₅ : ∀ j, tableSlot ≤ j → j < slots → s₅.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32 :=
    fun j h1 h2 => by have := sl₅ j h1 h2; simp only [slotW, sb₅, base₄] at this; exact this
  obtain sc₅ : ScrOk s₀ b E s₅.mem := sc₄.frame hfit' f₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dTab.sub_left subTab
  obtain hk₄ : ∀ j < 16, tableKeys s₄ j = keyPairs E j := fun j hj => by
    simp only [tableKeys, keyPairs, slotW, base₄]
    rw [sc₄.keys _ (by omega_arith), show tableSlot + 2 * j + 1 = tableSlot + (2 * j + 1) by omega_arith,
      sc₄.keys _ (by omega_arith)]
  obtain wr₅ : s₅.wr = s.wr := by rw [wr₅', wr₄']
  obtain rd₅ : s₅.rd = s.rd := by rw [rd₅', rd₄, rd₄a, rd₃]
  obtain sp₅ : s₅.sp = s.sp := by rw [sp₅', sp₄, sp₄a, sp₃]
  obtain hwS₅ : ScrIn s₅.wr b := by rw [wr₅]; exact hwS
  -- The data pointer and the blocks left back.
  obtain ⟨s₆a, e₆a, r₆a, o₆a, m₆a, rd₆a, wr₆a, sp₆a⟩ := ldSlot_ok s₅ .r1 sb (k := ptrSlot) base₅ (by decide) hwS₅
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := ldSlot_ok s₆a .r2 sb (k := cntSlot)
    (by rw [o₆a _ (by decide), base₅]) (by decide) (by rw [wr₆a]; exact hwS₅)
  refine WP.of_runBlock ⟨s₆, by
    rw [show ([ldS .r1 ptrSlot, ldS .r2 cntSlot] : List Instr) =
      [.ldr .r1 sb (4 * ptrSlot)] ++ [.ldr .r2 sb (4 * cntSlot)] from rfl, runBlock_append, e₆a, Option.bind_some, e₆],
    ?_⟩
  obtain r1₆ : s₆.gpr .r1 = A := by rw [o₆ _ (by decide), r₆a, keep₅ _ (by decide) (by decide), dp₄]
  obtain r2₆ : s₆.gpr .r2 = BitVec.ofNat 32 v := by rw [r₆, m₆a, keep₅ _ (by decide) (by decide), np₄]
  obtain base₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), o₆a _ (by decide), base₅]
  obtain mem₆ : s₆.mem = s₅.mem := by rw [m₆, m₆a]
  obtain wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₆a, wr₅]
  obtain rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₆a, rd₅]
  obtain sp₆' : s₆.sp = s.sp := by rw [sp₆, sp₆a, sp₅]
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r2₆ hv) fun s₇ ⟨r3₇, o₇, m₇, rd₇, wr₇, sp₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a, sp₈a⟩ := addImm_ok s₇ .r0 sb (BitVec.ofNat 32 (4 * tailSlot)) (by decide)
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈, sp₈⟩ := movR_ok s₈a .r12 .r1
  obtain mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈a, m₇, mem₆]
  obtain g₈ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₈.gpr r = s₆.gpr r :=
    fun r h0 h12 h3 h4 => by rw [o₈ r h12, o₈a r h0, o₇ r h3 h4]
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [show ([tailAddr .r0, movR .r12 .r1] : List Instr) =
      [.dp .add .r0 sb (.imm (BitVec.ofNat 32 (4 * tailSlot)))] ++ [movR .r12 .r1] from rfl,
      runBlock_append, e₈a, Option.bind_some]; exact e₈, ?_⟩)
  obtain rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈a, rd₇, rd₆']
  obtain wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈a, wr₇, wr₆']
  refine WP.mono (copyBlocks_wp (A := T) (B := A) hc0 hc8 hTn hAn
    (fun t ht h4 => by rw [rd₈', wr₈']; exact inRd (inT t ht h4))
    (fun t ht h4 => by rw [wr₈']; exact inA t ht h4) sepAT.symm
    ⟨by rw [o₈ _ (by decide), r₈a, o₇ _ (by decide) (by decide), base₆]; simp [T],
      by rw [r₈, o₈a _ (by decide), o₇ _ (by decide) (by decide), r1₆]; simp [A],
      by rw [o₈ _ (by decide), o₈a _ (by decide), r3₇, Nat.sub_zero], ⟨fun t ht => by omega_arith, Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s₉ h₉ => ?_
  obtain f₉ : Frame [⟨State.addr A, 16 * c⟩] s₅.mem s₉.mem := by rw [← mem₈]; exact h₉.cp.frame
  obtain g₉ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₉.gpr r = s₆.gpr r :=
    fun r h0 h12 h3 h4 => by rw [h₉.regs r h0 h12 h3 h4, g₈ r h0 h12 h3 h4]
  obtain sc₉ : ScrOk s₀ b E s₉.mem := sc₅.frame hfit' f₉ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dA.sub_left subTab
  obtain wr₉ : s₉.wr = s.wr := by rw [h₉.wr, wr₈']
  obtain rd₉ : s₉.rd = s.rd := by rw [h₉.rd, rd₈']
  obtain sp₉ : s₉.sp = s.sp := by rw [h₉.sp, sp₈, sp₈a, sp₇, sp₆']
  -- The blocks the eight-block code read are the group's, as on entry.
  obtain hblk : ∀ j < c, tailBlock s₄ j =
      Spec.Seed.blockAt s₀.mem (State.addr D + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Seed.blockAt, Vector.getElem_ofFn]
    have := h₃.cp.copied (16 * j + u) (by omega_arith)
    rw [hT, VG.Offset.add_add, hA, VG.Offset.add_add] at this
    obtain hout : ∀ r ∈ [(⟨wordAddr b ptrSlot, 4⟩ : Region), ⟨wordAddr b cntSlot, 4⟩],
        ¬ r.Contains (State.addr b + BitVec.ofNat 64 (4 * tailSlot + (16 * j + u))) 1 := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [ptrSlot_eq, cntSlot_eq]); omega_arith)] <;>
        exact not_contains_off _ (by (try simp only [tailSlot_eq, ptrSlot_eq, cntSlot_eq]); omega_arith)
          (by rw [tailSlot_eq]; omega_arith) (by omega_arith) (by (try simp only [ptrSlot_eq, cntSlot_eq]); omega_arith)
    rw [base₄, VG.Offset.add_add, show 4 * tailSlot + 16 * j + u = 4 * tailSlot + (16 * j + u) by omega_arith,
      fs _ hout, this, mem₂, hi.data _ (by omega_arith), ite_eq_right (by omega_arith), VG.Offset.add_add,
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega_arith]
  obtain hdata : DInv s₀.mem s₉.mem (State.addr D) n (8 * k + c) (outF s₀.mem (State.addr D) E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : State.addr D + BitVec.ofNat 64 i = State.addr A + BitVec.ofNat 64 (i - 128 * k) := by
        rw [hA, VG.Offset.add_add, show 128 * k + (i - 128 * k) = i by omega_arith]
      rw [e1, h₉.cp.copied _ (by omega_arith), mem₈, ite_eq_left (show i < 16 * (8 * k + c) by omega_arith),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega_arith, show i % 16 = (i - 128 * k) % 16 by omega_arith]
      obtain hj : (i - 128 * k) / 16 < c := by omega_arith
      obtain eT : State.addr T + BitVec.ofNat 64 (i - 128 * k) =
          State.addr (s₅.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * ((i - 128 * k) / 16)) +
            BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [base₅, hT, VG.Offset.add_add, VG.Offset.add_add,
          show 4 * tailSlot + 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 = 4 * tailSlot + (i - 128 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (tailBlock s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj, Proof.Seed.crypt_congr hk₄]
      rfl
    · have hout : ∀ r ∈ [(⟨State.addr A, 16 * c⟩ : Region)], ¬ r.Contains (State.addr D + BitVec.ofNat 64 i) 1 :=
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [hA]
          exact not_contains_off _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      rw [f₉ _ hout,
        f₅.bytes (R := ⟨State.addr D, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)) (by simp only; omega_arith) hin,
        fs.bytes (R := ⟨State.addr D, 16 * n⟩) (dD hsub) (by simp only; omega_arith) hin,
        f₃.bytes (R := ⟨State.addr D, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subT) (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega_arith), ite_eq_left (show i < 16 * (8 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega_arith)]
  obtain fr₉ : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s.mem s₉.mem := by
    refine ((f₃.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((fs.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, hsub r hr⟩).trans
      ((f₅.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₉.sub fun r hr => ⟨⟨State.addr D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩))))
    · simp only [List.mem_singleton] at hr; subst hr; exact subT
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact subA
  -- On to the next group.
  obtain r2₉ : s₉.gpr .r2 = BitVec.ofNat 32 v := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), r2₆]
  unfold advance
  refine WP.seq (WP.mono (groupCount_wp r2₉ hv) fun s₁₀ ⟨r3₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀, sp₁₀⟩ => ?_)
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁, sp₁₁⟩ := addImm_ok s₁₀ .r1 .r1 128 (by decide)
  obtain ⟨s₁₂, e₁₂, r₁₂, z₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂, sp₁₂⟩ := subsR_ok s₁₁ .r2 .r2 .r3
  refine WP.of_runBlock ⟨s₁₂, by
    rw [show ([.dp .add .r1 .r1 (.imm 128), .subs .r2 .r2 (.reg .r3)] : List Instr) =
      [.dp .add .r1 .r1 (.imm 128)] ++ [.subs .r2 .r2 (.reg .r3)] from rfl,
      runBlock_append, e₁₁, Option.bind_some, e₁₂], ?_⟩
  obtain zz : s₁₂.z = decide (v = c) := by
    rw [z₁₂, o₁₁ _ (by decide), o₁₁ _ (by decide), r3₁₀, o₁₀ _ (by decide) (by decide), r2₉,
      ofNat32_sub_beq (by omega_arith) (by omega_arith)]
  obtain hmem : s₁₂.mem = s₉.mem := by rw [m₁₂, m₁₁, m₁₀]
  obtain base₁₂ : s₁₂.gpr sb = b := by
    rw [o₁₂ _ (by decide), o₁₁ _ (by decide), o₁₀ _ (by decide) (by decide),
      g₉ _ (by decide) (by decide) (by decide) (by decide), base₆]
  obtain rd₁₂' : s₁₂.rd = s₀.rd := by rw [rd₁₂, rd₁₁, rd₁₀, rd₉, hi.rd]
  obtain wr₁₂' : s₁₂.wr = s₀.wr := by rw [wr₁₂, wr₁₁, wr₁₀, wr₉, hi.wr]
  obtain sp₁₂' : s₁₂.sp = s₀.sp := by rw [sp₁₂, sp₁₁, sp₁₀, sp₉, hi.sp]
  obtain fr : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s₁₂.mem := by
    rw [hmem]; exact hi.frame.trans fr₉
  by_cases hlt : v ≤ 8
  · have hn : 8 * k + c = n := by omega_arith
    refine .inl ⟨by rw [zz]; simp; omega_arith, base₁₂, hmem ▸ sc₉, by have := hmem ▸ hdata; rwa [hn] at this, fr,
      rd₁₂', wr₁₂', sp₁₂'⟩
  · have hc : c = 8 := by omega_arith
    refine .inr ⟨by rw [zz]; simp; omega_arith, base₁₂, ?_, ?_, by omega_arith, hmem ▸ sc₉,
      by rw [hmem, show 8 * (k + 1) = 8 * k + c by omega_arith]; exact hdata, fr, rd₁₂', wr₁₂', sp₁₂'⟩
    · rw [o₁₂ _ (by decide), r₁₁, o₁₀ _ (by decide) (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide),
        r1₆]
      simp only [A]
      rw [show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, VG.Offset.add_add,
        show 128 * k + 128 = 128 * (k + 1) by omega_arith]
    · rw [r₁₂, o₁₁ _ (by decide), o₁₁ _ (by decide), r3₁₀, o₁₀ _ (by decide) (by decide), r2₉,
        VG.Offset.ofNat_sub_ofNat (by omega_arith), show v - c = n - 8 * (k + 1) by omega_arith]

end VG.Proof.Seed.Arm
