module

public import VerifiedGarbage.Proof.Seed.X86.Lanes
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Seed.Rounds
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Seed.X86.Round`, which only this module used -/

section

/-! ### `Seed.X86.Steps`, which only this module used -/

section

/-!
# The steps of a round, lane by lane

As on ARMv7 (`Proof/Seed/Arm/Steps.lean`): each step of the round
(`step1` … `step4`) on one lane meets its `LaneSpec` (`LaneOk`); `lanes_ok`
then gives it on all eight. The halves `L` and `R` are at `l` and `r`, the
arrays of `L0`/`R0`, whose second words are 8 slots on.
-/

@[expose] public section

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

end

end


/-!
# A round on x86 (32-bit)

`g8_lanes` restates `g8_ok` on the lanes of the arrays, and `round_ok` puts
the steps of a round together, as on ARMv7 (`Proof/Seed/Arm/Round.lean`):
on every lane, `round l r`, with `L` at `l` and `R` at `r`, does RFC 4269
§2's round (`Spec.Seed.round`, which then exchanges the halves) to
`(L0, L1, R0, R1)`, with the round key in the slots `k` and `k + 1`, at
`kp`: the new `L` is the old `R`, at `r`, and the new `R` is at `l`
(`quadAt`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Seed.X86
open VG.Impl.Aes.X86 (sb slotAt movS st xorR xorS addI at_ tmpRegs)
open VG.X86.Straight (wordAddr Ok slotRegion)

theorem room_ok_gCfg {s : State} (h : Room s) : Ok gCfg s where
  slotIn k hk := h.inR (by simp [gCfg] at hk; rw [slots_eq]; omega_arith)
  extIn k hk := by simp [gCfg] at hk
  fit := by have := h.fit; simp [gCfg, slots_eq] at this ⊢; omega_arith
  sep k _ j hj := by simp [gCfg] at hj

/-- `g8` on the lanes: `G` of `G`'s words, the other arrays and the slots
from the arrays' kept. -/
theorem g8_lanes {s : State} (h : Room s) :
    ∃ s', runBlock isa g8 s = some s' ∧
      (∀ w < 8, lv s' (tSlot 0) w = Spec.Seed.g (lv s (tSlot 0) w)) ∧
      (∀ k, 80 ≤ k → k < slots → slotW s' k = slotW s k) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧ Frame [workR s] s.mem s'.mem := by
  obtain ⟨s', hs', hg, hrd, hwr, hregs, hfr⟩ := g8_ok (room_ok_gCfg h)
  obtain hsb : s'.gpr sb = s.gpr sb := hregs _ (by decide)
  obtain hf := h.fit; rw [slots_eq] at hf
  have := toNat_addr (s.gpr sb)
  refine ⟨s', hs', fun w hw => ?_, fun k hk1 hk2 => ?_, h.congr hsb hwr, hrd, hwr, hregs, ?_⟩
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
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r) := by
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

theorem keepRegs : ∀ r ∈ [Reg.esp, .esi, .edi], r ≠ .eax ∧ r ≠ .ebx ∧ r ∉ tmpRegs := by decide

/-- The round key at `kp`, slots `k` and `k + 1`. -/
def KeyAt (s : State) (k : Nat) : Prop := s.gpr kp = s.gpr sb + BitVec.ofNat 32 (4 * k)

theorem round_ok {l r : Nat} (hl : l ∈ halves) (hr : r ∈ halves) (hlr : l ≠ r) {s : State} (h : Room s)
    {k : Nat} (hk2 : k + 1 < slots) (hkp : KeyAt s k) :
    ∃ s', runBlock isa (round l r) s = some s' ∧
      (∀ b < 8, quadAt s' r l b = Spec.Seed.round (slotW s k, slotW s (k + 1)) (quadAt s l r b)) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr kp = s.gpr kp + 8 ∧ s'.gpr sb = s.gpr sb ∧ s'.gpr .esp = s.gpr .esp ∧
      (∀ j, tailSlot ≤ j → j < slots → slotW s' j = slotW s j) ∧
      Frame [workR s] s.mem s'.mem := by
  obtain hf := h.fit; rw [slots_eq] at hf hk2
  have hT : tailSlot = 136 := rfl
  let K0 := slotW s k
  let K1 := slotW s (k + 1)
  obtain ⟨hL, hL8, hLt, hLa, hLc, hLd, hL8t, hL8a, hL8c, hL8d, hLL⟩ := half_mem hl
  obtain ⟨hR, hR8, hRt, hRa, hRc, hRd, hR8t, hR8a, hR8c, hR8d, hRR⟩ := half_mem hr
  obtain hlr8 : l ≠ r + 8 ∧ l + 8 ≠ r ∧ l + 8 ≠ r + 8 := by
    simp only [halves, List.mem_cons, List.not_mem_nil, or_false] at hl hr
    rcases hl with rfl | rfl <;> rcases hr with rfl | rfl <;> first | exact absurd rfl hlr | decide
  -- The round key.
  obtain ea0 : s.ea (at_ kp 0) = slotA s k := by
    show addr (s.gpr kp) 0 = _
    rw [hkp, X86.Straight.addr_add_ofNat]; rfl
  obtain ea4 : s.ea (at_ kp 4) = slotA s (k + 1) := by
    show addr (s.gpr kp) 4 = _
    rw [hkp, X86.Straight.addr_add_ofNat, show 4 * k + 4 = 4 * (k + 1) by omega_arith]
  obtain e1 : exec (.mov .ecx (.mem (at_ kp 0))) s = some (s.setReg .ecx K0) := by
    simp only [exec, readSrc, ea0, load_slot h (show k < slots by rw [slots_eq]; omega_arith), Option.map_some]
    rfl
  obtain e2 : exec (.mov .edx (.mem (at_ kp 4))) (s.setReg .ecx K0) = some ((s.setReg .ecx K0).setReg .edx K1) := by
    obtain ea4' : (s.setReg .ecx K0).ea (at_ kp 4) = slotA s (k + 1) := by
      show addr ((s.setReg .ecx K0).gpr kp) 4 = _
      rw [gpr_setReg_of_ne _ _ (by decide)]; exact ea4
    simp only [exec, readSrc, ea4', show (s.setReg .ecx K0).load32 (slotA s (k + 1)) = some K1 from
      load_slot (s := s.setReg .ecx K0) (room_setReg h (by decide) _) (show k + 1 < slots by rw [slots_eq]; omega_arith),
      Option.map_some]
  let s2 := (s.setReg .ecx K0).setReg .edx K1
  obtain hrun2 : runBlock isa [.mov .ecx (.mem (at_ kp 0)), .mov .edx (.mem (at_ kp 4))] s = some s2 := by
    rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_nil]
  obtain g2 : ∀ r, r ≠ .ecx → r ≠ .edx → s2.gpr r = s.gpr r := fun r h1 h2 => by
    simp only [s2, gpr_setReg_of_ne _ _ h1, gpr_setReg_of_ne _ _ h2]
  obtain h2 : Room s2 := room_setReg (room_setReg h (by decide) _) (by decide) _
  obtain hkeys : KeysIn K0 K1 s2 := ⟨h2, by
      show ((s.setReg .ecx K0).setReg .edx K1).gpr .ecx = K0
      rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_self], gpr_setReg_self _ _ _⟩
  obtain lv2 : ∀ k b, lv s2 k b = lv s k b := fun k b => by
    simp only [lv, s2, slotW_setReg _ (show Reg.edx ≠ sb by decide), slotW_setReg _ (show Reg.ecx ≠ sb by decide)]
  -- The steps.
  obtain ⟨s3, hs3, hP3, hv3, fr3, rd3, wr3, rg3⟩ := lanes_ok (dests1 (r := r) K0 K1) (reads1 hr K0 K1)
    (P := KeysIn K0 K1)
    (fun _ s s' hP hok => ⟨hP.1.congr (hok.regs _ (by decide) (by decide)) hok.wr,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.1,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.2⟩)
    (fun _ h => h.1) (fun b hb s hs => step1_ok hr K0 K1 hb s hs) hkeys 8 (Nat.le_refl _)
  obtain ⟨s4, hs4, hg4, hk4, h4, rd4, wr4, rg4, fr4⟩ := g8_lanes hP3.1
  obtain ⟨s5, hs5, h5, hv5, fr5, rd5, wr5, rg5⟩ :=
    lanes8_room dests2 reads2 (fun b hb s hs => step2_ok hb s hs) h4
  obtain ⟨s6, hs6, hg6, hk6, h6, rd6, wr6, rg6, fr6⟩ := g8_lanes h5
  obtain ⟨s7, hs7, h7, hv7, fr7, rd7, wr7, rg7⟩ :=
    lanes8_room dests3 reads3 (fun b hb s hs => step3_ok hb s hs) h6
  obtain ⟨s8, hs8, hg8, hk8, h8, rd8, wr8, rg8, fr8⟩ := g8_lanes h7
  obtain ⟨s9, hs9, h9, hv9, fr9, rd9, wr9, rg9⟩ :=
    lanes8_room (dests4 hl) (reads4 hl) (fun b hb s hs => step4_ok hl hb s hs) h8
  let s10 := (arithFlags s9 (s9.gpr kp + 8) (2 ^ 32 ≤ (s9.gpr kp).toNat + (8 : BitVec 32).toNat)
    (addOverflow (s9.gpr kp) 8 (s9.gpr kp + 8))).setReg kp (s9.gpr kp + 8)
  obtain hrun : runBlock isa [addI kp 8] s9 = some s10 := by
    rw [runBlock_cons, show exec (addI kp 8) s9 = some s10 from rfl, runStep_some, runBlock_nil]
  -- Registers through the steps.
  obtain keep : ∀ r ∈ [Reg.esp, .esi, .edi], s9.gpr r = s.gpr r := by
    intro r hr
    obtain ⟨h1, h2, hg⟩ := keepRegs r hr
    obtain h3 : r ≠ .ecx ∧ r ≠ .edx := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide
    rw [rg9 r h1 h2, rg8 r hg, rg7 r h1 h2, rg6 r hg, rg5 r h1 h2, rg4 r hg, rg3 r h1 h2, g2 r h3.1 h3.2]
  obtain sb9 : s9.gpr sb = s.gpr sb := keep _ (by decide)
  obtain sb10 : s10.gpr sb = s.gpr sb := by rw [gpr_setReg_of_ne _ _ (by decide)]; exact sb9
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
    simp only [s10, mem_setReg, mem_arithFlags]
    refine (fc (g2 _ (by decide) (by decide)) (work_of_arrays fr3)).trans ?_
    refine (fc sb3 fr4).trans ?_
    refine (fc sb4 (work_of_arrays fr5)).trans ?_
    refine (fc sb5 fr6).trans ?_
    refine (fc sb6 (work_of_arrays fr7)).trans ?_
    refine (fc sb7 fr8).trans ?_
    exact fc sb8 (work_of_arrays fr9)
  refine ⟨s10, ?_, fun b hb => ?_, h9.congr (gpr_setReg_of_ne _ _ (by decide)) rfl, ?_, ?_, ?_, sb10, ?_,
    fun j hj1 hj2 => ?_, frame⟩
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
      obtain hk56 : 80 ≤ k := by
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
      obtain hk56 : 80 ≤ k := by
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
      obtain hk56 : 80 ≤ k := by
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
  · simp only [s10, rd_setReg, rd_arithFlags, rd9, rd8, rd7, rd6, rd5, rd4, rd3]; rfl
  · simp only [s10, wr_setReg, wr_arithFlags, wr9, wr8, wr7, wr6, wr5, wr4, wr3]; rfl
  · rw [show s10.gpr kp = s9.gpr kp + 8 from gpr_setReg_self _ _ _, show s9.gpr kp = s.gpr kp from keep _ (by decide)]
  · rw [show s10.gpr .esp = s9.gpr .esp from gpr_setReg_of_ne _ _ (by decide)]; exact keep _ (by decide)
  · rw [show slotW s10 j = slotW s9 j from slotW_setReg _ (by decide) _ _]
    exact slot_keep_work h (by simpa only [s10, mem_setReg, mem_arithFlags] using frame) sb9 hj1 hj2

end VG.Proof.Seed.X86

end

end


/-!
# Eight blocks of SEED on x86 (32-bit)

`crypt8_wp`: `crypt8` turns each of the eight blocks of the tail buffer into
`Spec.Seed.crypt` of it, with round `j + 1`'s key in the table's slots
`tableSlot + 2j` and `tableSlot + 2j + 1` (`tableKeys`). It copies the
blocks' words, byte-reversed, to the arrays (`toArr`, by `moves_ok`), runs
the eight pairs of rounds (`rounds_wp`), and copies the arrays back, `R`
first (`fromArr`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Seed.X86 VG.Proof.Seed
open VG.Impl.Aes.X86 (sb slotAt movS st xorR xorS addI subI movI movR subR at_)
open VG.X86.Straight (wordAddr)

/-! ## Single instructions -/

/-- `add d, v`. -/
theorem addI_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [addI d v] s = some s' ∧ s'.gpr d = s.gpr d + v ∧
      s'.zf = some (s.gpr d + v == 0) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨(arithFlags s (s.gpr d + v) (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat) (addOverflow (s.gpr d) v (s.gpr d + v))).setReg d
      (s.gpr d + v), rfl, gpr_setReg_self _ _ _, rfl, fun _ hr => gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl⟩

/-- `sub d, v`. -/
theorem subI_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [VG.Impl.Aes.X86.subI d v] s = some s' ∧ s'.gpr d = s.gpr d - v ∧
      s'.zf = some (s.gpr d - v == 0) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨(arithFlags s (s.gpr d - v) ((s.gpr d).toNat < v.toNat) (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d
      (s.gpr d - v), rfl, gpr_setReg_self _ _ _, rfl, fun _ hr => gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl⟩

/-- `mov d, s`. -/
theorem movR_ok (s : State) (d r₀ : Reg) :
    ∃ s', runBlock isa [movR d r₀] s = some s' ∧ s'.gpr d = s.gpr r₀ ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      s'.cf = s.cf :=
  ⟨s.setReg d (s.gpr r₀), rfl, gpr_setReg_self _ _ _, fun _ hr => gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl, rfl, rfl⟩

/-- `mov d, v`. -/
theorem movI_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [VG.Impl.Aes.X86.movI d v] s = some s' ∧ s'.gpr d = v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg d v, rfl, gpr_setReg_self _ _ _, fun _ hr => gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl⟩

/-- `mov eax, kp; sub eax, edi; cmp eax, v`. -/
theorem endTest_ok (s : State) (v : BitVec 32) :
    ∃ s', runBlock isa [movR .eax kp, subR .eax .edi, .alu .cmp .eax (.imm v)] s = some s' ∧
      s'.zf = some (s.gpr kp - s.gpr .edi - v == 0) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁, -, -⟩ := movR_ok s .eax kp
  obtain ⟨s₂, e₂, r₂, -, o₂, m₂, rd₂, wr₂⟩ := subI_ok s₁ .eax (s₁.gpr .edi)
  let s₃ := arithFlags s₂ (s₂.gpr .eax - v) ((s₂.gpr .eax).toNat < v.toNat) (subOverflow (s₂.gpr .eax) v (s₂.gpr .eax - v))
  refine ⟨s₃, ?_, ?_, fun r hr => by rw [gpr_arithFlags, o₂ r hr, o₁ r hr], by rw [mem_arithFlags, m₂, m₁],
    by rw [rd_arithFlags, rd₂, rd₁], by rw [wr_arithFlags, wr₂, wr₁]⟩
  · rw [show ([movR .eax kp, subR .eax .edi, .alu .cmp .eax (.imm v)] : List Instr) =
      [movR .eax kp] ++ ([subR .eax .edi] ++ [.alu .cmp .eax (.imm v)]) from rfl, runBlock_append, e₁, Option.bind_some,
      runBlock_append, show runBlock isa [subR .eax .edi] s₁ = runBlock isa [VG.Impl.Aes.X86.subI .eax (s₁.gpr .edi)] s₁ from rfl,
      e₂, Option.bind_some]
    rfl
  · rw [zf_arithFlags, r₂, r₁, o₁ _ (by decide)]

theorem ofNat32_sub_beq {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

theorem eval_ne (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl
theorem eval_e (s : State) : isa.eval .e s = s.zf := rfl
theorem eval_b (s : State) : isa.eval .b s = s.cf := rfl

/-! ## Moving words between slots, byte-reversed -/

/-- `mov eax, [edi + 4 a]; bswap eax; mov [edi + 4 d], eax` for each `(a, d)`. -/
def movesCode (L : List (Nat × Nat)) : List Instr := L.flatMap fun p => [movS .eax p.1, .bswap .eax, st p.2 .eax]

theorem moves_ok {s : State} (h : Room s) {n : Nat} (hn : n ≤ slots) :
    ∀ (L : List (Nat × Nat)), (∀ p ∈ L, p.1 < slots ∧ p.2 < n) → (∀ p ∈ L, ∀ q ∈ L, p.1 ≠ q.2) →
      (L.map (·.2)).Nodup →
      ∃ s', runBlock isa (movesCode L) s = some s' ∧
        (∀ p ∈ L, slotW s' p.2 = byteRev32 (slotW s p.1)) ∧
        (∀ j < slots, j ∉ L.map (·.2) → slotW s' j = slotW s j) ∧
        (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        Frame [⟨(s.gpr sb).setWidth 64, 4 * n⟩] s.mem s'.mem
  | [], _, _, _ => ⟨s, runBlock_nil, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | p :: L, hL, hd, hnd => by
    obtain hp := hL p List.mem_cons_self
    obtain hpd : p.2 < slots := by omega_arith
    let s₁ := setMem ((s.setReg .eax (slotW s p.1)).setReg .eax (bswap (slotW s p.1)))
      (s.mem.writeW (slotA s p.2) (bswap (slotW s p.1)))
    obtain e₁ : runBlock isa [movS .eax p.1, .bswap .eax, st p.2 .eax] s = some s₁ := by
      rw [runBlock_cons, exec_movS h hp.1, runStep_some, runBlock_cons,
        show exec (.bswap .eax) (s.setReg .eax (slotW s p.1)) =
          some ((s.setReg .eax (slotW s p.1)).setReg .eax (bswap (slotW s p.1))) by
          simp [exec, gpr_setReg_self],
        runStep_some, runBlock_cons,
        exec_st (room_setReg (room_setReg h (by decide) _) (by decide) _) hpd, runStep_some, runBlock_nil]
      simp only [s₁, slotA_setReg _ (show Reg.eax ≠ sb by decide), gpr_setReg_self, mem_setReg]
    obtain h₁ : Room s₁ := room_setMem (room_setReg (room_setReg h (by decide) _) (by decide) _) _
    obtain sb₁ : s₁.gpr sb = s.gpr sb := by
      simp only [s₁, gpr_setMem, gpr_setReg_of_ne _ _ (show sb ≠ .eax by decide)]
    obtain sl₁ : ∀ j < slots, slotW s₁ j = if j = p.2 then bswap (slotW s p.1) else slotW s j := by
      intro j hj
      rw [show s₁ = setMem _ _ from rfl, slotW_setMem, slotA_setReg _ (by decide), slotA_setReg _ (by decide)]
      exact slotW_setMem_write h hpd hj _
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := moves_ok h₁ hn L (fun q hq => hL q (List.mem_cons_of_mem _ hq))
      (fun q hq q' hq' => hd q (List.mem_cons_of_mem _ hq) q' (List.mem_cons_of_mem _ hq')) hnd.2
    have hfit := h.fit
    refine ⟨s', ?_, fun q hq => ?_, fun j hj hjL => ?_, fun r hr => ?_, by rw [rd']; rfl, by rw [wr']; rfl, ?_⟩
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
      show Frame _ s.mem (s.mem.writeW (slotA s p.2) (bswap (slotW s p.1)))
      refine (Frame.refl _ _).writeW List.mem_cons_self _ ?_
      rw [slots_eq] at hfit hn
      exact Straight.slot_contains _ hp.2 (by omega_arith)

/-! ## The blocks and the arrays -/

/-- Block `b` of the tail buffer. -/
abbrev tailBlock (s : State) (b : Nat) : Spec.Seed.Block :=
  Spec.Seed.blockAt s.mem ((s.gpr sb).setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * b))

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
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [workR s] s.mem s'.mem := by
  obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := moves_ok h (n := tailSlot) (by decide) toArrMoves
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨s', ?_, fun w hw b hb => ?_, fun j hj1 hj2 => o' j hj1 ?_, g', rd', wr', f'⟩
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
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨(s.gpr sb).setWidth 64, 4 * tableSlot⟩] s.mem s'.mem := by
  obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := moves_ok h (n := tableSlot) (by decide) fromArrMoves
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨s', ?_, fun w hw b hb => ?_, fun j hj1 hj2 => o' j hj1 ?_, g', rd', wr', f'⟩
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
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ KeyAt s' (k + 4) ∧ s'.gpr sb = s.gpr sb ∧
      s'.gpr .esp = s.gpr .esp ∧
      (∀ j, tailSlot ≤ j → j < slots → slotW s' j = slotW s j) ∧ Frame [workR s] s.mem s'.mem ∧
      s'.zf = some (decide (k + 4 = tableEnd)) := by
  have hT : tableEnd = 200 := rfl
  have hS : tableSlot = 168 := rfl
  obtain ⟨s₁, e₁, q₁, h₁, rd₁, wr₁, kp₁, sb₁, sp₁, sl₁, f₁⟩ :=
    round_ok halves0 halves2 (by decide) h (k := k) (by rw [slots_eq]; omega_arith) hkp
  obtain hkp₁ : KeyAt s₁ (k + 2) := by
    rw [KeyAt, kp₁, hkp, sb₁, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Offset.add_add]
    rfl
  obtain ⟨s₂, e₂, q₂, h₂, rd₂, wr₂, kp₂, sb₂, sp₂, sl₂, f₂⟩ :=
    round_ok halves2 halves0 (by decide) h₁ (k := k + 2) (by rw [slots_eq]; omega_arith) hkp₁
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := endTest_ok s₂ (BitVec.ofNat 32 (4 * tableEnd))
  obtain sb₃ : s₃.gpr sb = s.gpr sb := by rw [g₃ _ (by decide), sb₂, sb₁]
  obtain hkp₂ : s₂.gpr kp = s.gpr sb + BitVec.ofNat 32 (4 * (k + 4)) := by
    rw [kp₂, hkp₁, sb₁, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Offset.add_add]
    rfl
  obtain sl₃ : ∀ j, slotW s₃ j = slotW s₂ j := fun j => by simp only [slotW, m₃, g₃ sb (by decide)]
  have hfit := h.fit
  rw [slots_eq] at hfit
  refine ⟨s₃, ?_, fun b hb => ?_, h₂.congr (g₃ _ (by decide)) wr₃, by rw [rd₃, rd₂, rd₁],
    by rw [wr₃, wr₂, wr₁], ?_, sb₃, by rw [g₃ _ (by decide), sp₂, sp₁], fun j hj1 hj2 => ?_, ?_, ?_⟩
  · rw [roundPair, runBlock_append, runBlock_append, e₁, Option.bind_some, e₂, Option.bind_some, e₃]
  · have e : quadAt s₃ (arrSlot 0) (arrSlot 2) b = quadAt s₂ (arrSlot 0) (arrSlot 2) b := by
      simp only [quadAt, lv, sl₃]
    rw [e, q₂ b hb, q₁ b hb, sl₁ _ (by simp [tailSlot]; omega_arith) (by rw [slots_eq]; omega_arith),
      sl₁ _ (by simp [tailSlot]; omega_arith) (by rw [slots_eq]; omega_arith)]
  · rw [KeyAt, g₃ _ (by decide), hkp₂, sb₃]
  · rw [sl₃, sl₂ j hj1 hj2, sl₁ j hj1 hj2]
  · rw [m₃]; exact f₁.trans (by simpa [workR, sb₁] using f₂)
  · have e2 : s₂.gpr .edi = s.gpr sb := by rw [show s₂.gpr .edi = s₂.gpr sb from rfl, sb₂, sb₁]
    rw [z₃, hkp₂, e2, Offset.add_sub_cancel_left, ofNat32_sub_beq (by omega_arith) (by omega_arith)]
    simp only [Option.some.injEq, decide_eq_decide]; omega_arith

/-- The sixteen rounds, round `j + 1`'s key in the table's slots
`tableSlot + 2j` and `tableSlot + 2j + 1`. -/
theorem rounds_wp {s₀ : State} (h : Room s₀) :
    WP isa rounds s₀ fun s' =>
      (∀ b < 8, quadAt s' (arrSlot 0) (arrSlot 2) b =
        roundsN (tableKeys s₀) 16 (quadAt s₀ (arrSlot 0) (arrSlot 2) b)) ∧
      Room s' ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.gpr sb = s₀.gpr sb ∧ s'.gpr .esp = s₀.gpr .esp ∧
      (∀ j, tailSlot ≤ j → j < slots → slotW s' j = slotW s₀ j) ∧ Frame [workR s₀] s₀.mem s'.mem := by
  obtain ⟨s₁a, e₁a, k₁a, o₁a, m₁a, rd₁a, wr₁a, -, -⟩ := movR_ok s₀ kp .edi
  obtain ⟨s₁, e₁, k₁, -, o₁, m₁, rd₁, wr₁⟩ := addI_ok s₁a kp (BitVec.ofNat 32 (4 * tableSlot))
  obtain sb₁ : s₁.gpr sb = s₀.gpr sb := by rw [o₁ _ (by decide), o₁a _ (by decide)]
  obtain sp₁ : s₁.gpr .esp = s₀.gpr .esp := by rw [o₁ _ (by decide), o₁a _ (by decide)]
  obtain sl₁ : ∀ j, slotW s₁ j = slotW s₀ j := fun j => by simp only [slotW, m₁, m₁a, sb₁]
  refine WP.seq (WP.of_runBlock ⟨s₁, by
    rw [kpAt, show ([movR kp .edi, addI kp (BitVec.ofNat 32 (4 * tableSlot))] : List Instr) =
      [movR kp .edi] ++ [addI kp (BitVec.ofNat 32 (4 * tableSlot))] from rfl, runBlock_append, e₁a,
      Option.bind_some, e₁], ?_⟩)
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = 8 - m ∧ m < 8 ∧ Room s ∧ s.gpr sb = s₀.gpr sb ∧
    s.gpr .esp = s₀.gpr .esp ∧ KeyAt s (tableSlot + 4 * m) ∧
    (∀ b < 8, quadAt s (arrSlot 0) (arrSlot 2) b =
      roundsN (tableKeys s₀) (2 * m) (quadAt s₀ (arrSlot 0) (arrSlot 2) b)) ∧
    s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    (∀ j, tailSlot ≤ j → j < slots → slotW s j = slotW s₀ j) ∧ Frame [workR s₀] s₀.mem s.mem
  refine WP.loop (M := isa) Inv (fun n s hs => ?_) 8 s₁
    ⟨0, rfl, by omega_arith, h.congr sb₁ (by rw [wr₁, wr₁a]), sb₁, sp₁,
      by rw [KeyAt, k₁, k₁a, sb₁]; rfl,
      fun b _ => by simp only [quadAt, lv, sl₁]; rfl, by rw [rd₁, rd₁a], by rw [wr₁, wr₁a], fun j _ _ => sl₁ j,
      by rw [m₁, m₁a]; exact Frame.refl _ _⟩
  obtain ⟨m, rfl, hm8, hR, hsb, hsp, hkp, hq, hrd, hwr, hsl, hf⟩ := hs
  obtain ⟨s', e', q', R', rd', wr', kp', sb', sp', sl', f', z'⟩ :=
    roundPair_ok hR (k := tableSlot + 4 * m) (by simp [tableEnd]; omega_arith) (by omega_arith) hkp
  obtain hkeys : ∀ i < 4, slotW s (tableSlot + 4 * m + i) = slotW s₀ (tableSlot + 4 * m + i) := fun i hi =>
    hsl _ (by simp [tailSlot, tableSlot]; omega_arith) (by rw [slots_eq]; simp [tableSlot]; omega_arith)
  obtain inv' : ∀ b < 8, quadAt s' (arrSlot 0) (arrSlot 2) b =
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
  obtain hf' : Frame [workR s₀] s₀.mem s'.mem := hf.trans (by simpa [workR, hsb] using f')
  obtain hsl' : ∀ j, tailSlot ≤ j → j < slots → slotW s' j = slotW s₀ j := fun j h1 h2 => by
    rw [sl' j h1 h2, hsl j h1 h2]
  by_cases h8 : m + 1 = 8
  · refine .inl ⟨by rw [eval_ne, z']; simp [tableEnd]; omega_arith, fun b hb => ?_, R', by rw [rd', hrd],
      by rw [wr', hwr], by rw [sb', hsb], by rw [sp', hsp], hsl', hf'⟩
    rw [inv' b hb, h8]
  · refine .inr ⟨by rw [eval_ne, z']; simp [tableEnd]; omega_arith, 8 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith,
      R', by rw [sb', hsb], by rw [sp', hsp],
      by rw [show tableSlot + 4 * (m + 1) = tableSlot + 4 * m + 4 by omega_arith]; exact kp', inv', by rw [rd', hrd],
      by rw [wr', hwr], hsl', hf'⟩

/-! ## Eight blocks -/

/-- Byte `j` (in memory order) of a byte-reversed word is byte `3 - j` of the word. -/
theorem byteRev32_byte (x : BitVec 32) {j : Nat} (hj : j < 4) :
    (byteRev32 x).extractLsb' (8 * j) 8 = (x >>> (8 * (3 - j))).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain h4 := Proof.Seed.getLsbD_append4 (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8)
    (x.extractLsb' 24 8) hi
  obtain e : ((byteRev32 x).extractLsb' (8 * j) 8).getLsbD i = (byteRev32 x).getLsbD (8 * j + i) := by
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
    (s.gpr sb).setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * b) + BitVec.ofNat 64 (4 * w) =
      slotA s (tailAt b w) := by
  obtain hf := h.fit; rw [slots_eq] at hf
  rw [slotA, slot_addr (by simp [tailAt, tailSlot]; omega_arith), Offset.add_add]
  congr 2; simp [tailAt]; omega_arith

theorem crypt8_wp {s₀ : State} (h : Room s₀) :
    WP isa crypt8 s₀ fun s' =>
      (∀ b < 8, tailBlock s' b = Spec.Seed.crypt (tableKeys s₀) (tailBlock s₀ b)) ∧
      Room s' ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.gpr sb = s₀.gpr sb ∧ s'.gpr .esp = s₀.gpr .esp ∧
      (∀ j, tableSlot ≤ j → j < slots → slotW s' j = slotW s₀ j) ∧
      Frame [⟨(s₀.gpr sb).setWidth 64, 4 * tableSlot⟩] s₀.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, g₁, rd₁, wr₁, f₁⟩ := toArr_ok h
  obtain sb₁ : s₁.gpr sb = s₀.gpr sb := g₁ _ (by decide)
  obtain h₁ : Room s₁ := h.congr sb₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (rounds_wp h₁) fun s₂ ⟨q₂, h₂, rd₂, wr₂, sb₂, sp₂, sl₂, f₂⟩ => ?_)
  obtain ⟨s₃, e₃, v₃, o₃, g₃, rd₃, wr₃, f₃⟩ := fromArr_ok h₂
  refine WP.of_runBlock ⟨s₃, e₃, ?_⟩
  obtain sb₃ : s₃.gpr sb = s₀.gpr sb := by rw [g₃ _ (by decide), sb₂, sb₁]
  have hfit := h.fit
  rw [slots_eq] at hfit
  obtain hkeys : ∀ j < 16, tableKeys s₀ j = tableKeys s₁ j := by
    intro j hj
    simp only [tableKeys]
    rw [o₁ _ (by rw [slots_eq]; simp [tableSlot]; omega_arith) (by simp [tailSlot, tableSlot]; omega_arith),
      o₁ _ (by rw [slots_eq]; simp [tableSlot]; omega_arith) (by simp [tailSlot, tableSlot]; omega_arith)]
  -- The blocks, in the arrays.
  obtain hin : ∀ b < 8, decodeQ (tailBlock s₀ b) = quadAt s₁ (arrSlot 0) (arrSlot 2) b := by
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
    by rw [wr₃, wr₂, wr₁], sb₃, by rw [g₃ _ (by decide), sp₂, g₁ _ (by decide)], fun j hj1 hj2 => ?_, ?_⟩
  · rw [crypt_eq, hin b hb, roundsN_congr 16 _ hkeys, ← q₂ b hb]
    apply Vector.ext
    intro i hi
    obtain h₃ : Room s₃ := h₂.congr (by rw [g₃ _ (by decide)]) wr₃
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

end VG.Proof.Seed.X86
