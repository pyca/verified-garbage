import VerifiedGarbage.Proof.Seed.Arm.Ecb
import VerifiedGarbage.Proof.Seed.KeySchedule
import VerifiedGarbage.Impl.Seed.Arm.ExpandKey

/-!
# A round of the key schedule on ARMv7

`keyRound_ok`: `keyRound j` writes round `j + 1`'s two inputs of `G`
(`gInput`), from `Key0 … Key3` in `r4`–`r7`, to their slots, and rotates
`Key0 || Key1` or `Key2 || Key3` as one 64-bit word (`rotr8_hi`, …: a
rotation of `a || b` by eight bits is two shifts of each word); `keyRounds_ok`
runs the sixteen.
-/

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Seed.Arm VG.Proof.Seed
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS lsrOp imm32)
open VG.Arm.Straight (wordAddr)

/-! ## Rotations of 64-bit words, as two 32-bit words -/

theorem getLsbD_congr (x : BitVec 32) {i j : Nat} (h : i = j) : x.getLsbD i = x.getLsbD j := by rw [h]

theorem rotr8_hi (a b : BitVec 32) : ((a ++ b).rotateRight 8).extractLsb' 32 32 = a >>> 8 ||| b <<< 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight, BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 24 with h | h
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), getLsbD_congr a (show 8 % (32 + 32) + (32 + i) - 32 = 8 + i by omega)]
    simp [h]
  · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    simp only [show 32 + i < 32 + 32 by omega, decide_true, Bool.true_and, show ¬ i < 24 by omega, decide_false,
      Bool.not_false]
    rw [getLsbD_congr b (show 32 + i - (32 + 32 - 8 % (32 + 32)) = i - 24 by omega), BitVec.getLsbD_of_ge a (8 + i) (by omega)]
    simp

theorem rotr8_lo (a b : BitVec 32) : ((a ++ b).rotateRight 8).setWidth 32 = b >>> 8 ||| a <<< 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_rotateRight, BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 24 with h | h
  · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    simp [h]
  · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    simp only [show ¬ i < 24 by omega, decide_false, Bool.not_false, Bool.true_and]
    rw [getLsbD_congr a (show 8 % (32 + 32) + i - 32 = i - 24 by omega), BitVec.getLsbD_of_ge b (8 + i) (by omega)]
    simp

theorem rotl8_hi (a b : BitVec 32) : ((a ++ b).rotateLeft 8).extractLsb' 32 32 = a <<< 8 ||| b >>> 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateLeft, BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rw [ite_eq_right (by omega)]
  simp only [show 32 + i < 32 + 32 by omega, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 8 with h | h
  · rw [ite_eq_left (by omega), getLsbD_congr b (show 32 + i - 8 % (32 + 32) = 24 + i by omega)]
    simp [h]
  · rw [ite_eq_right (by omega), getLsbD_congr a (show 32 + i - 8 % (32 + 32) - 32 = i - 8 by omega),
      BitVec.getLsbD_of_ge b (24 + i) (by omega)]
    simp [show ¬ i < 8 by omega]

theorem rotl8_lo (a b : BitVec 32) : ((a ++ b).rotateLeft 8).setWidth 32 = b <<< 8 ||| a >>> 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_rotateLeft, BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 8 with h | h
  · rw [ite_eq_left (by omega), ite_eq_right (by omega),
      getLsbD_congr a (show 32 + 32 - 8 % (32 + 32) + i - 32 = 24 + i by omega)]
    simp [h]
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), getLsbD_congr b (show i - 8 % (32 + 32) = i - 8 by omega),
      BitVec.getLsbD_of_ge a (24 + i) (by omega)]
    simp [show ¬ i < 8 by omega, show i < 32 + 32 by omega]

/-! ## Instructions -/

theorem exec_subR (s : State) (d n m : Reg) :
    exec (subR d n m) s = some (s.setReg d (s.gpr n - s.gpr m)) := rfl

theorem exec_movR (s : State) (d n : Reg) : exec (movR d n) s = some (s.setReg d (s.gpr n)) := rfl

theorem exec_mov_lsr (s : State) (d r : Reg) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) :
    exec (.mov d (lsrOp r n)) s = some (s.setReg d (s.gpr r >>> n)) := by
  simp [exec, Op2.eval, lsrOp, h1, h2]

theorem exec_mov_lsl (s : State) (d r : Reg) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) :
    exec (.mov d (lslOp r n)) s = some (s.setReg d (s.gpr r <<< n)) := by
  simp [exec, Op2.eval, lslOp, h1, h2]

theorem exec_orr_lsr (s : State) (d m r : Reg) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) :
    exec (.dp .orr d m (lsrOp r n)) s = some (s.setReg d (s.gpr m ||| s.gpr r >>> n)) := by
  simp [exec, Op2.eval, lsrOp, h1, h2]

theorem exec_orr_lsl (s : State) (d m r : Reg) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) :
    exec (.dp .orr d m (lslOp r n)) s = some (s.setReg d (s.gpr m ||| s.gpr r <<< n)) := by
  simp [exec, Op2.eval, lslOp, h1, h2]

/-! ## The rotations -/

/-- The key words in `r4`–`r7`. -/
def kw (s : State) : Quad := (s.gpr .r4, s.gpr .r5, s.gpr .r6, s.gpr .r7)

/-- The registers a round of the key schedule writes. -/
def keyRegs : List Reg := [t0, t1, .r4, .r5, .r6, .r7]

theorem rotr8_ok (s : State) :
    ∃ s', runBlock isa (rotr8 .r4 .r5) s = some s' ∧
      kw s' = keyStep 0 (kw s) ∧ (∀ r ∉ keyRegs, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [rotr8, runBlock_cons, exec_mov_lsr _ _ _ (by decide) (by decide), runStep_some, runBlock_cons,
    exec_orr_lsl _ _ _ _ (by decide) (by decide), runStep_some, runBlock_cons,
    exec_mov_lsr _ _ _ (by decide) (by decide), runStep_some, runBlock_cons,
    exec_orr_lsl _ _ _ _ (by decide) (by decide), runStep_some, runBlock_cons, exec_movR, runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [kw, keyStep, Nat.zero_mod, gpr_setReg, t0, t1, reduceCtorEq, ↓reduceIte,
      rotr8_hi, rotr8_lo]
  · simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ↓reduceIte]

theorem rotl8_ok (s : State) :
    ∃ s', runBlock isa (rotl8 .r6 .r7) s = some s' ∧
      kw s' = keyStep 1 (kw s) ∧ (∀ r ∉ keyRegs, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [rotl8, runBlock_cons, exec_mov_lsl _ _ _ (by decide) (by decide), runStep_some, runBlock_cons,
    exec_orr_lsr _ _ _ _ (by decide) (by decide), runStep_some, runBlock_cons,
    exec_mov_lsl _ _ _ (by decide) (by decide), runStep_some, runBlock_cons,
    exec_orr_lsr _ _ _ _ (by decide) (by decide), runStep_some, runBlock_cons, exec_movR, runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [kw, keyStep, show 1 % 2 = 1 from rfl, gpr_setReg, t0, t1, reduceCtorEq, ↓reduceIte,
      rotl8_hi, rotl8_lo]
  · simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ↓reduceIte]

/-! ## A round -/

/-- A round's inputs of `G`, before the rotation. -/
def keyIn (j : Nat) : List Instr :=
  [addR t0 .r4 .r6] ++ imm32 t1 (Spec.Seed.kc.getD j 0) ++
  [subR t0 t0 t1, stS (uSlot (2 * j)) t0, subR t0 .r5 .r7, addR t0 t0 t1, stS (uSlot (2 * j + 1)) t0]

theorem keyRound_eq (j : Nat) :
    keyRound j = keyIn j ++ (if j % 2 = 0 then rotr8 .r4 .r5 else rotl8 .r6 .r7) := by
  simp only [keyRound, keyIn, List.append_assoc]

theorem uSlot_lt {i : Nat} (hi : i < 32) : uSlot i < slots := by simp [uSlot, aSlot, slots_eq]; omega

theorem keyIn_ok {j : Nat} (hj : j < 16) {s : State} (h : Room s) :
    ∃ s', runBlock isa (keyIn j) s = some s' ∧
      slotW s' (uSlot (2 * j)) = s.gpr .r4 + s.gpr .r6 - Spec.Seed.kc.getD j 0 ∧
      slotW s' (uSlot (2 * j + 1)) = s.gpr .r5 - s.gpr .r7 + Spec.Seed.kc.getD j 0 ∧
      (∀ k < slots, k ≠ uSlot (2 * j) → k ≠ uSlot (2 * j + 1) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [workR s] s.mem s'.mem := by
  have hu0 := uSlot_lt (i := 2 * j) (by omega)
  have hu1 := uSlot_lt (i := 2 * j + 1) (by omega)
  have hR : ∀ {t : State} (r : Reg) (v : BitVec 32), Room t → r ≠ sb → Room (t.setReg r v) :=
    fun r v ht hr => room_setReg ht hr v
  rw [show keyIn j = [addR t0 .r4 .r6, .movw t1 ((Spec.Seed.kc.getD j 0).extractLsb' 0 16),
      .movt t1 ((Spec.Seed.kc.getD j 0).extractLsb' 16 16), subR t0 t0 t1, stS (uSlot (2 * j)) t0,
      subR t0 .r5 .r7, addR t0 t0 t1, stS (uSlot (2 * j + 1)) t0] from rfl,
    runBlock_cons, exec_addR, runStep_some, runBlock_cons,
    show ∀ t : State, exec (.movw t1 ((Spec.Seed.kc.getD j 0).extractLsb' 0 16)) t =
      some (t.setReg t1 (((Spec.Seed.kc.getD j 0).extractLsb' 0 16).setWidth 32)) from fun _ => rfl,
    runStep_some, runBlock_cons,
    show ∀ t : State, exec (.movt t1 ((Spec.Seed.kc.getD j 0).extractLsb' 16 16)) t =
      some (t.setReg t1 ((Spec.Seed.kc.getD j 0).extractLsb' 16 16 ++ (t.gpr t1).extractLsb' 0 16)) from
      fun _ => rfl,
    runStep_some, runBlock_cons, exec_subR, runStep_some, runBlock_cons,
    exec_stS (hR _ _ (hR _ _ (hR _ _ (hR _ _ h (by decide)) (by decide)) (by decide)) (by decide)) hu0,
    runStep_some, runBlock_cons, exec_subR, runStep_some, runBlock_cons, exec_addR, runStep_some,
    runBlock_cons, exec_stS (hR _ _ (hR _ _ (room_setMem (hR _ _ (hR _ _ (hR _ _ (hR _ _ h (by decide))
      (by decide)) (by decide)) (by decide)) _) (by decide)) (by decide)) hu1,
    runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ?_, fun k hk1 hk2 hk3 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, ?_⟩
  · simp (disch := decide) only [slotW_setMem, slotA_setReg, slotA_setMem, gpr_setReg_self, mem_setMem,
      mem_setReg, movw_movt]
    rw [Mem.readW_writeW_sep (Straight.slot_sep _ (by have := h.fit; rw [slots_eq] at hu0 hu1 this; omega)
      (by have := h.fit; rw [slots_eq] at hu0 hu1 this; omega) (by simp [uSlot])) (by decide),
      Mem.readW_writeW_self32]
    simp only [gpr_setReg, t0, t1, reduceCtorEq, ↓reduceIte]
  · simp (disch := decide) only [slotW_setMem, slotA_setReg, slotA_setMem, gpr_setReg_self, mem_setMem,
      mem_setReg, Mem.readW_writeW_self32, movw_movt]
    simp only [gpr_setReg, gpr_setMem, t0, t1, reduceCtorEq, ↓reduceIte]
  · simp (disch := decide) only [slotW_setMem, slotA_setReg, slotA_setMem, mem_setMem, mem_setReg]
    have hf := h.fit; rw [slots_eq] at hk1 hu0 hu1 hf
    rw [Mem.readW_writeW_sep (Straight.slot_sep _ (by omega) (by omega) hk3) (by decide),
      Mem.readW_writeW_sep (Straight.slot_sep _ (by omega) (by omega) hk2) (by decide)]
    rfl
  · simp only [gpr_setMem, gpr_setReg_of_ne _ _ h1, gpr_setReg_of_ne _ _ h2]
  · simp (disch := decide) only [mem_setMem, mem_setReg, slotA_setReg, slotA_setMem]
    have hf := h.fit; rw [slots_eq] at hu0 hu1 hf
    have hw : ∀ i < 32, (workR s).Contains (slotA s (uSlot i)) 4 := fun i hi => by
      rw [slotA, slot_addr (by simp [uSlot, aSlot]; omega)]
      exact Offset.contains_base _ (by simp [uSlot, aSlot, tailSlot]; omega) (by simp [uSlot, aSlot]; omega)
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (hw _ (by omega))).writeW List.mem_cons_self _
      (hw _ (by omega))

theorem keyRound_ok {j : Nat} (hj : j < 16) {s : State} (h : Room s) :
    ∃ s', runBlock isa (keyRound j) s = some s' ∧ kw s' = keyStep j (kw s) ∧
      slotW s' (uSlot (2 * j)) = (kw s).1 + (kw s).2.2.1 - Spec.Seed.kc.getD j 0 ∧
      slotW s' (uSlot (2 * j + 1)) = (kw s).2.1 - (kw s).2.2.2 + Spec.Seed.kc.getD j 0 ∧
      (∀ k < slots, k ≠ uSlot (2 * j) → k ≠ uSlot (2 * j + 1) → slotW s' k = slotW s k) ∧
      (∀ r ∉ keyRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [workR s] s.mem s'.mem := by
  obtain ⟨s₁, e₁, a₁, b₁, o₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := keyIn_ok hj h
  have k₁ : kw s₁ = kw s := by
    simp only [kw, g₁ .r4 (by decide) (by decide), g₁ .r5 (by decide) (by decide), g₁ .r6 (by decide) (by decide),
      g₁ .r7 (by decide) (by decide)]
  have rot : ∃ s₂, runBlock isa (if j % 2 = 0 then rotr8 .r4 .r5 else rotl8 .r6 .r7) s₁ = some s₂ ∧
      kw s₂ = keyStep j (kw s₁) ∧ (∀ r ∉ keyRegs, s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.sp = s₁.sp := by
    by_cases he : j % 2 = 0
    · rw [ite_eq_left he]
      obtain ⟨s₂, e₂, k₂, rest⟩ := rotr8_ok s₁
      exact ⟨s₂, e₂, by rw [k₂]; simp only [keyStep, he, Nat.zero_mod, ite_true], rest⟩
    · rw [ite_eq_right he]
      obtain ⟨s₂, e₂, k₂, rest⟩ := rotl8_ok s₁
      exact ⟨s₂, e₂, by rw [k₂]; simp only [keyStep, he, show 1 % 2 = 1 from rfl]; rfl, rest⟩
  obtain ⟨s₂, e₂, k₂, g₂, m₂, rd₂, wr₂, sp₂⟩ := rot
  have sb₂ : s₂.gpr sb = s.gpr sb := by rw [g₂ _ (by decide), g₁ _ (by decide) (by decide)]
  have sl₂ : ∀ k, slotW s₂ k = slotW s₁ k := fun k => by
    simp only [slotW, m₂, g₂ sb (by decide)]
  refine ⟨s₂, by rw [keyRound_eq, runBlock_append, e₁, Option.bind_some, e₂], by rw [k₂, k₁],
    by rw [sl₂, a₁]; rfl, by rw [sl₂, b₁]; rfl, fun k h1 h2 h3 => by rw [sl₂, o₁ k h1 h2 h3],
    fun r hr => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁], by rw [m₂]; exact f₁⟩
  have : r ≠ t0 ∧ r ≠ t1 := by
    simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact ⟨hr.1, hr.2.1⟩
  rw [g₂ r hr, g₁ r this.1 this.2]

/-- The inputs of `G` from round `j + 1`'s key words. -/
theorem gInput_even (key : Spec.Seed.Block) (j : Nat) :
    gInput key (2 * j) = (keyWords key j).1 + (keyWords key j).2.2.1 - Spec.Seed.kc.getD j 0 := by
  simp only [gInput, show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega, ite_true]

theorem gInput_odd (key : Spec.Seed.Block) (j : Nat) :
    gInput key (2 * j + 1) = (keyWords key j).2.1 - (keyWords key j).2.2.2 + Spec.Seed.kc.getD j 0 := by
  simp only [gInput, show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]; rfl

/-- The first `n` rounds of the key schedule. -/
theorem keyRounds_ok (key : Spec.Seed.Block) {s : State} (h : Room s) (hk : kw s = keyWords key 0) :
    ∀ n ≤ 16, ∃ s', runBlock isa ((List.range n).flatMap keyRound) s = some s' ∧ Room s' ∧
      kw s' = keyWords key n ∧ (∀ i < 2 * n, slotW s' (uSlot i) = gInput key i) ∧
      (∀ k < slots, (k < uSlot 0 ∨ uSlot (2 * n) ≤ k) → slotW s' k = slotW s k) ∧
      (∀ r ∉ keyRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [workR s] s.mem s'.mem := by
  intro n hn
  induction n with
  | zero => exact ⟨s, runBlock_nil, h, hk, fun i hi => by omega, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, e₁, h₁, k₁, v₁, o₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := ih (by omega)
    obtain ⟨s₂, e₂, k₂, a₂, b₂, o₂, g₂, rd₂, wr₂, sp₂, f₂⟩ := keyRound_ok (j := n) (by omega) h₁
    have sb₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide)
    have sb₂ : s₂.gpr sb = s.gpr sb := by rw [g₂ _ (by decide), sb₁]
    refine ⟨s₂, ?_, h.congr sb₂ (by rw [wr₂, wr₁]), by rw [k₂, k₁]; rfl, fun i hi => ?_, fun k hk1 hk2 => ?_,
      fun r hr => by rw [g₂ r hr, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁],
      f₁.trans (by simpa [workR, sb₁] using f₂)⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_append, e₁, Option.bind_some, List.flatMap_singleton, e₂]
    · rcases (show i < 2 * n ∨ i = 2 * n ∨ i = 2 * n + 1 by omega) with hi' | rfl | rfl
      · rw [o₂ _ (uSlot_lt (by omega)) (by simp [uSlot]; omega) (by simp [uSlot]; omega), v₁ i hi']
      · rw [a₂, k₁, gInput_even]
      · rw [b₂, k₁, gInput_odd]
    · rw [o₂ k hk1 (by simp [uSlot] at hk2 ⊢; omega) (by simp [uSlot] at hk2 ⊢; omega),
        o₁ k hk1 (by simp [uSlot] at hk2 ⊢; omega)]

end VG.Proof.Seed.Arm
