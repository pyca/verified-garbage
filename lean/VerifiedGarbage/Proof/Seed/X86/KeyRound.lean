import VerifiedGarbage.Proof.Seed.X86.Ecb
import VerifiedGarbage.Proof.Seed.KeyRot
import VerifiedGarbage.Impl.Seed.X86.ExpandKey

/-!
# A round of the key schedule on x86 (32-bit)

`keyRound_ok`: `keyRound j` writes round `j + 1`'s two inputs of `G`
(`gInput`), from `Key0 … Key3` in the slots `keySlot w`, to their slots,
and rotates `Key0 || Key1` or `Key2 || Key3` as one 64-bit word: each word
rotated by eight or 24 bits, and their bytes exchanged under a mask
(`xr_hi`, …), which is two shifts of each word, as `keyStep` has it
(`rotr8_hi`, …); `keyRounds_ok` runs the sixteen.
-/

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Seed.X86 VG.Proof.Seed
open VG.Impl.Aes.X86 (sb slotAt movS st movR xorR addI subI rorI andI)
open VG.X86.Straight (wordAddr)

/-! ## The rotations, bit by bit -/

theorem maskHi_bit : ∀ i < 32, ((0xFF000000 : BitVec 32)).getLsbD i = decide (24 ≤ i) := by decide
theorem maskLo_bit : ∀ i < 32, ((0x000000FF : BitVec 32)).getLsbD i = decide (i < 8) := by decide

theorem xr_hi (a b : BitVec 32) :
    a.rotateRight 8 ^^^ ((a.rotateRight 8 ^^^ b.rotateRight 8) &&& (0xFF000000 : BitVec 32)) = a >>> 8 ||| b <<< 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, maskHi_bit i hi, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 24 with h | h
  · simp [h, show ¬ 24 ≤ i by omega]
  · simp only [show 24 ≤ i by omega, show ¬ i < 24 by omega, decide_true,
      decide_false, ite_false, Bool.and_true, Bool.not_false, Bool.true_and]
    rw [getLsbD_congr b (show i - (32 - 8 % 32) = i - 24 by omega), BitVec.getLsbD_of_ge a (8 + i) (by omega)]
    cases a.getLsbD (i - (32 - 8 % 32)) <;> cases b.getLsbD (i - 24) <;> rfl

theorem xr_lo (a b : BitVec 32) :
    b.rotateRight 8 ^^^ ((a.rotateRight 8 ^^^ b.rotateRight 8) &&& (0xFF000000 : BitVec 32)) = b >>> 8 ||| a <<< 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, maskHi_bit i hi, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 24 with h | h
  · simp [h, show ¬ 24 ≤ i by omega]
  · simp only [show 24 ≤ i by omega, show ¬ i < 24 by omega, decide_true,
      decide_false, ite_false, Bool.and_true, Bool.not_false, Bool.true_and]
    rw [getLsbD_congr a (show i - (32 - 8 % 32) = i - 24 by omega), BitVec.getLsbD_of_ge b (8 + i) (by omega)]
    cases a.getLsbD (i - 24) <;> cases b.getLsbD (i - (32 - 8 % 32)) <;> rfl

theorem xl_hi (a b : BitVec 32) :
    a.rotateRight 24 ^^^ ((a.rotateRight 24 ^^^ b.rotateRight 24) &&& (0x000000FF : BitVec 32)) = a <<< 8 ||| b >>> 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, maskLo_bit i hi, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 8 with h | h
  · simp only [h, decide_true, ite_true, Bool.and_true, Bool.not_true,
      Bool.false_and, Bool.false_or]
    rw [getLsbD_congr b (show 24 % 32 + i = 24 + i by omega)]
    cases a.getLsbD (24 % 32 + i) <;> cases b.getLsbD (24 + i) <;> rfl
  · simp [show ¬ i < 8 by omega,
      BitVec.getLsbD_of_ge b (24 + i) (by omega)]

theorem xl_lo (a b : BitVec 32) :
    b.rotateRight 24 ^^^ ((a.rotateRight 24 ^^^ b.rotateRight 24) &&& (0x000000FF : BitVec 32)) = b <<< 8 ||| a >>> 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, maskLo_bit i hi, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 8 with h | h
  · simp only [h, decide_true, ite_true, Bool.and_true, Bool.not_true,
      Bool.false_and, Bool.false_or]
    rw [getLsbD_congr a (show 24 % 32 + i = 24 + i by omega)]
    cases a.getLsbD (24 + i) <;> cases b.getLsbD (24 % 32 + i) <;> rfl
  · simp [show ¬ i < 8 by omega,
      BitVec.getLsbD_of_ge a (24 + i) (by omega)]

/-! ## Instructions -/

theorem exec_movS' {k : Nat} (hk : k < slots) (d : Reg) {s : State} (h : Room s) :
    exec (movS d k) s = some (s.setReg d (slotW s k)) := exec_movS h hk d

theorem exec_st' {k : Nat} (hk : k < slots) (r : Reg) {s : State} (h : Room s) :
    exec (st k r) s = some (setMem s (s.mem.writeW (slotA s k) (s.gpr r))) := exec_st h hk r

theorem exec_addS' {k : Nat} (hk : k < slots) (d : Reg) {s : State} (h : Room s) :
    exec (addS d k) s =
      some ((arithFlags s (s.gpr d + slotW s k) (2 ^ 32 ≤ (s.gpr d).toNat + (slotW s k).toNat)
        (addOverflow (s.gpr d) (slotW s k) (s.gpr d + slotW s k))).setReg d (s.gpr d + slotW s k)) :=
  exec_addS h hk d

theorem exec_subS' {k : Nat} (hk : k < slots) (d : Reg) {s : State} (h : Room s) :
    exec (subS d k) s =
      some ((arithFlags s (s.gpr d - slotW s k) ((s.gpr d).toNat < (slotW s k).toNat)
        (subOverflow (s.gpr d) (slotW s k) (s.gpr d - slotW s k))).setReg d (s.gpr d - slotW s k)) := by
  simp only [subS, exec, execAlu, readSrc, ea_slot, load_slot h hk, Option.bind_some]

/-- The flags `ror d, n` sets. -/
def rorF (s : State) (d : Reg) (n : Nat) : State :=
  s.setFlags (some ((s.gpr d).rotateRight n).msb)
    (if n = 1 then some (((s.gpr d).rotateRight n).msb ^^ ((s.gpr d).rotateRight n).getMsbD 1) else none) s.zf s.sf

theorem gpr_rorF (s : State) (d : Reg) (n : Nat) : (rorF s d n).gpr = s.gpr := rfl
theorem mem_rorF (s : State) (d : Reg) (n : Nat) : (rorF s d n).mem = s.mem := rfl
theorem rd_rorF (s : State) (d : Reg) (n : Nat) : (rorF s d n).rd = s.rd := rfl
theorem wr_rorF (s : State) (d : Reg) (n : Nat) : (rorF s d n).wr = s.wr := rfl

theorem exec_rorI {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) (s : State) (d : Reg) :
    exec (rorI d n) s = some ((rorF s d n).setReg d ((s.gpr d).rotateRight n)) := by
  simp only [rorI, exec, execShift, h1, h2, and_self, ite_true]; rfl

theorem exec_andI (s : State) (d : Reg) (v : BitVec 32) :
    exec (andI d v) s = some ((arithFlags s (s.gpr d &&& v) false false).setReg d (s.gpr d &&& v)) := rfl

theorem exec_movR (s : State) (d r : Reg) : exec (movR d r) s = some (s.setReg d (s.gpr r)) := rfl

theorem exec_addI (s : State) (d : Reg) (v : BitVec 32) :
    exec (addI d v) s = some ((arithFlags s (s.gpr d + v) (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)
      (addOverflow (s.gpr d) v (s.gpr d + v))).setReg d (s.gpr d + v)) := rfl

theorem exec_subI (s : State) (d : Reg) (v : BitVec 32) :
    exec (subI d v) s = some ((arithFlags s (s.gpr d - v) ((s.gpr d).toNat < v.toNat)
      (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d (s.gpr d - v)) := rfl

/-- Room through the writes of registers other than `sb`. -/
macro "room" : tactic => `(tactic|
  (refine Room.congr ‹Room _› ?_ ?_
   · simp only [gpr_setReg, gpr_arithFlags, gpr_rorF, gpr_setMem, sb, reduceCtorEq, ↓reduceIte]
   · rfl))

/-- The key's words. -/
def kwS (s : State) : Quad := (slotW s (keySlot 0), slotW s (keySlot 1), slotW s (keySlot 2), slotW s (keySlot 3))

theorem keySlot_lt {w : Nat} (hw : w < 4) : keySlot w < slots := by simp [keySlot, tailSlot, slots_eq]; omega

/-! ## The rotations -/

theorem rot64_ok {k n : Nat} (hk : k ≤ 2) (h1 : 1 ≤ n) (h2 : n ≤ 31) (m : BitVec 32) {s : State} (h : Room s) :
    ∃ s', runBlock isa (rot64 k n m) s = some s' ∧
      slotW s' (keySlot k) = (slotW s (keySlot k)).rotateRight n ^^^
        (((slotW s (keySlot k)).rotateRight n ^^^ (slotW s (keySlot (k + 1))).rotateRight n) &&& m) ∧
      slotW s' (keySlot (k + 1)) = (slotW s (keySlot (k + 1))).rotateRight n ^^^
        (((slotW s (keySlot k)).rotateRight n ^^^ (slotW s (keySlot (k + 1))).rotateRight n) &&& m) ∧
      (∀ j < slots, j ≠ keySlot k → j ≠ keySlot (k + 1) → slotW s' j = slotW s j) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s] s.mem s'.mem := by
  have hk0 := keySlot_lt (w := k) (by omega)
  have hk1 := keySlot_lt (w := k + 1) (by omega)
  rw [rot64, runBlock_cons, exec_movS' hk0 .eax, runStep_some, runBlock_cons, exec_rorI h1 h2, runStep_some,
    runBlock_cons, exec_movS' hk1 .ebx, runStep_some, runBlock_cons, exec_rorI h1 h2, runStep_some,
    runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_xorR, runStep_some, runBlock_cons, exec_andI,
    runStep_some, runBlock_cons, exec_xorR, runStep_some, runBlock_cons, exec_xorR, runStep_some,
    runBlock_cons, exec_st' hk0 .eax, runStep_some, runBlock_cons, exec_st' hk1 .ebx, runStep_some, runBlock_nil]
  have hf : (s.gpr .edi).toNat + 4 * slots ≤ 2 ^ 32 := h.fit
  have hne : keySlot k ≠ keySlot (k + 1) := by simp [keySlot]
  refine ⟨_, rfl, ?_, ?_, fun j hj h1 h2 => ?_, fun r h1 h2 h3 => ?_, rfl, rfl, ?_⟩
  · simp only [slotW, mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags, mem_rorF,
      gpr_rorF, slotA, sb, reduceCtorEq, ↓reduceIte]
    rw [readW_slot_write hf _ hk0 hk1, ite_eq_right hne, readW_slot_write hf _ hk0 hk0, ite_eq_left rfl]
  · simp only [slotW, mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags, mem_rorF,
      gpr_rorF, slotA, sb, reduceCtorEq, ↓reduceIte]
    rw [readW_slot_write hf _ hk1 hk1, ite_eq_left rfl]
  · simp only [slotW, mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags, mem_rorF,
      gpr_rorF, slotA, sb, reduceCtorEq, ↓reduceIte]
    rw [readW_slot_write hf _ hj hk1, ite_eq_right h2, readW_slot_write hf _ hj hk0, ite_eq_right h1]
  · simp only [gpr_setMem, gpr_setReg_of_ne _ _ h1, gpr_setReg_of_ne _ _ h2, gpr_setReg_of_ne _ _ h3,
      gpr_arithFlags, gpr_rorF]
  · simp only [mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags, mem_rorF,
      gpr_rorF, slotA, sb, reduceCtorEq, ↓reduceIte]
    have hc : ∀ w, w ≤ 3 → (scratchR s).Contains (wordAddr (s.gpr .edi) (keySlot w)) 4 := fun w hw =>
      slot_in h (keySlot_lt (by omega))
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (hc k (by omega))).writeW List.mem_cons_self _
      (hc (k + 1) (by omega))
  all_goals room

/-! ## A round -/

/-- A round's inputs of `G`, before the rotation. -/
def keyIn (j : Nat) : List Instr :=
  [movS .eax (keySlot 0), addS .eax (keySlot 2), subI .eax (Spec.Seed.kc.getD j 0), st (uSlot (2 * j)) .eax,
   movS .eax (keySlot 1), subS .eax (keySlot 3), addI .eax (Spec.Seed.kc.getD j 0), st (uSlot (2 * j + 1)) .eax]

theorem keyRound_eq (j : Nat) :
    keyRound j = keyIn j ++ (if j % 2 = 0 then rot64 0 8 0xFF000000 else rot64 2 24 0x000000FF) := rfl

theorem uSlot_lt {i : Nat} (hi : i < 32) : uSlot i < slots := by simp [uSlot, aSlot, slots_eq]; omega

theorem keyIn_ok {j : Nat} (hj : j < 16) {s : State} (h : Room s) :
    ∃ s', runBlock isa (keyIn j) s = some s' ∧
      slotW s' (uSlot (2 * j)) = (kwS s).1 + (kwS s).2.2.1 - Spec.Seed.kc.getD j 0 ∧
      slotW s' (uSlot (2 * j + 1)) = (kwS s).2.1 - (kwS s).2.2.2 + Spec.Seed.kc.getD j 0 ∧
      (∀ k < slots, k ≠ uSlot (2 * j) → k ≠ uSlot (2 * j + 1) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s] s.mem s'.mem := by
  have hu0 := uSlot_lt (i := 2 * j) (by omega)
  have hu1 := uSlot_lt (i := 2 * j + 1) (by omega)
  have hk : ∀ w < 4, keySlot w < slots := fun w hw => keySlot_lt hw
  have hf : (s.gpr .edi).toNat + 4 * slots ≤ 2 ^ 32 := h.fit
  have hne : ∀ w, keySlot w ≠ uSlot (2 * j) := fun w => by simp [keySlot, uSlot, aSlot, tailSlot]; omega
  have hne' : uSlot (2 * j + 1) ≠ uSlot (2 * j) := by simp [uSlot]
  rw [keyIn, runBlock_cons, exec_movS' (hk 0 (by decide)) .eax, runStep_some, runBlock_cons,
    exec_addS' (hk 2 (by decide)) .eax, runStep_some, runBlock_cons, exec_subI, runStep_some, runBlock_cons,
    exec_st' hu0 .eax, runStep_some, runBlock_cons, exec_movS' (hk 1 (by decide)) .eax, runStep_some,
    runBlock_cons, exec_subS' (hk 3 (by decide)) .eax, runStep_some, runBlock_cons, exec_addI, runStep_some,
    runBlock_cons, exec_st' hu1 .eax, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ?_, fun k hk' h1 h2 => ?_, fun r hr => ?_, rfl, rfl, ?_⟩
  · simp only [slotW, kwS, mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags,
      slotA, sb, reduceCtorEq, ↓reduceIte]
    rw [readW_slot_write hf _ hu0 hu1, ite_eq_right hne'.symm, readW_slot_write hf _ hu0 hu0, ite_eq_left rfl]
  · simp only [slotW, kwS, mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags,
      slotA, sb, reduceCtorEq, ↓reduceIte]
    rw [readW_slot_write hf _ hu1 hu1, ite_eq_left rfl, readW_slot_write hf _ (hk 1 (by decide)) hu0,
      ite_eq_right (hne 1), readW_slot_write hf _ (hk 3 (by decide)) hu0, ite_eq_right (hne 3)]
  · simp only [slotW, mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags,
      slotA, sb, reduceCtorEq, ↓reduceIte]
    rw [readW_slot_write hf _ hk' hu1, ite_eq_right h2, readW_slot_write hf _ hk' hu0, ite_eq_right h1]
  · simp only [gpr_setMem, gpr_setReg_of_ne _ _ hr, gpr_arithFlags]
  · simp only [mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags,
      slotA, sb, reduceCtorEq, ↓reduceIte]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (slot_in h hu0)).writeW List.mem_cons_self _
      (slot_in h hu1)
  all_goals room

theorem keyRound_ok {j : Nat} (hj : j < 16) {s : State} (h : Room s) :
    ∃ s', runBlock isa (keyRound j) s = some s' ∧ kwS s' = keyStep j (kwS s) ∧
      slotW s' (uSlot (2 * j)) = (kwS s).1 + (kwS s).2.2.1 - Spec.Seed.kc.getD j 0 ∧
      slotW s' (uSlot (2 * j + 1)) = (kwS s).2.1 - (kwS s).2.2.2 + Spec.Seed.kc.getD j 0 ∧
      (∀ k < slots, k ≠ uSlot (2 * j) → k ≠ uSlot (2 * j + 1) → (k < keySlot 0 ∨ keySlot 4 ≤ k) →
        slotW s' k = slotW s k) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨s₁, e₁, a₁, b₁, o₁, g₁, rd₁, wr₁, f₁⟩ := keyIn_ok hj h
  have sb₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide)
  have h₁ : Room s₁ := h.congr sb₁ wr₁
  have hne : ∀ w < 4, keySlot w ≠ uSlot (2 * j) ∧ keySlot w ≠ uSlot (2 * j + 1) := fun w hw => by
    simp [keySlot, uSlot, aSlot, tailSlot]; omega
  have k₁ : ∀ w < 4, slotW s₁ (keySlot w) = slotW s (keySlot w) := fun w hw =>
    o₁ _ (keySlot_lt hw) (hne w hw).1 (hne w hw).2
  have rot : ∃ s₂, runBlock isa (if j % 2 = 0 then rot64 0 8 0xFF000000 else rot64 2 24 0x000000FF) s₁ = some s₂ ∧
      kwS s₂ = keyStep j (kwS s) ∧
      (∀ k < slots, (k < keySlot 0 ∨ keySlot 4 ≤ k) → slotW s₂ k = slotW s₁ k) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧
      Frame [scratchR s₁] s₁.mem s₂.mem := by
    by_cases he : j % 2 = 0
    · rw [ite_eq_left he]
      obtain ⟨s₂, e₂, x₂, y₂, o₂, rest⟩ := rot64_ok (k := 0) (n := 8) (by decide) (by decide) (by decide) 0xFF000000 h₁
      refine ⟨s₂, e₂, ?_, fun k hk hk' => o₂ k hk (by simp only [keySlot, tailSlot] at hk' ⊢; omega)
        (by simp only [keySlot, tailSlot] at hk' ⊢; omega), rest⟩
      rw [keyStep, ite_eq_left he]; unfold kwS; dsimp only
      rw [x₂, y₂, o₂ _ (keySlot_lt (by decide)) (by simp [keySlot]) (by simp [keySlot]),
        o₂ _ (keySlot_lt (by decide)) (by simp [keySlot]) (by simp [keySlot]), k₁ 0 (by decide),
        k₁ 1 (by decide), k₁ 2 (by decide), k₁ 3 (by decide), xr_hi, xr_lo, rotr8_hi, rotr8_lo]
    · rw [ite_eq_right he]
      obtain ⟨s₂, e₂, x₂, y₂, o₂, rest⟩ := rot64_ok (k := 2) (n := 24) (by decide) (by decide) (by decide) 0x000000FF h₁
      refine ⟨s₂, e₂, ?_, fun k hk hk' => o₂ k hk (by simp only [keySlot, tailSlot] at hk' ⊢; omega)
        (by simp only [keySlot, tailSlot] at hk' ⊢; omega), rest⟩
      rw [keyStep, ite_eq_right he]; unfold kwS; dsimp only
      rw [x₂, y₂, o₂ _ (keySlot_lt (by decide)) (by simp [keySlot]) (by simp [keySlot]),
        o₂ _ (keySlot_lt (by decide)) (by simp [keySlot]) (by simp [keySlot]), k₁ 0 (by decide),
        k₁ 1 (by decide), k₁ 2 (by decide), k₁ 3 (by decide), xl_hi, xl_lo, rotl8_hi, rotl8_lo]
  obtain ⟨s₂, e₂, k₂, o₂, g₂, rd₂, wr₂, f₂⟩ := rot
  have hu0 : uSlot (2 * j) < keySlot 0 := by simp [keySlot, uSlot, aSlot, tailSlot]; omega
  have hu1 : uSlot (2 * j + 1) < keySlot 0 := by simp [keySlot, uSlot, aSlot, tailSlot]; omega
  refine ⟨s₂, by rw [keyRound_eq, runBlock_append, e₁, Option.bind_some, e₂], k₂,
    by rw [o₂ _ (uSlot_lt (by omega)) (.inl hu0), a₁], by rw [o₂ _ (uSlot_lt (by omega)) (.inl hu1), b₁],
    fun k hk h1 h2 h3 => by rw [o₂ k hk h3, o₁ k hk h1 h2], fun r h1 h2 h3 => by rw [g₂ r h1 h2 h3, g₁ r h1],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁], f₁.trans (by unfold scratchR at f₂ ⊢; rw [sb₁] at f₂; exact f₂)⟩

/-- The inputs of `G` from round `j + 1`'s key words. -/
theorem gInput_even (key : Spec.Seed.Block) (j : Nat) :
    gInput key (2 * j) = (keyWords key j).1 + (keyWords key j).2.2.1 - Spec.Seed.kc.getD j 0 := by
  simp only [gInput, show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega, ite_true]

theorem gInput_odd (key : Spec.Seed.Block) (j : Nat) :
    gInput key (2 * j + 1) = (keyWords key j).2.1 - (keyWords key j).2.2.2 + Spec.Seed.kc.getD j 0 := by
  simp only [gInput, show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]; rfl

/-- The first `n` rounds of the key schedule. -/
theorem keyRounds_ok (key : Spec.Seed.Block) {s : State} (h : Room s) (hk : kwS s = keyWords key 0) :
    ∀ n ≤ 16, ∃ s', runBlock isa ((List.range n).flatMap keyRound) s = some s' ∧ Room s' ∧
      kwS s' = keyWords key n ∧ (∀ i < 2 * n, slotW s' (uSlot i) = gInput key i) ∧
      (∀ k < slots, (k < uSlot 0 ∨ uSlot (2 * n) ≤ k) → (k < keySlot 0 ∨ keySlot 4 ≤ k) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s] s.mem s'.mem := by
  intro n hn
  induction n with
  | zero => exact ⟨s, runBlock_nil, h, hk, fun i hi => by omega, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl,
      Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, e₁, h₁, k₁, v₁, o₁, g₁, rd₁, wr₁, f₁⟩ := ih (by omega)
    obtain ⟨s₂, e₂, k₂, a₂, b₂, o₂, g₂, rd₂, wr₂, f₂⟩ := keyRound_ok (j := n) (by omega) h₁
    have sb₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide) (by decide) (by decide)
    have sb₂ : s₂.gpr sb = s.gpr sb := by rw [g₂ _ (by decide) (by decide) (by decide), sb₁]
    have hK : uSlot 32 ≤ keySlot 0 := by decide
    refine ⟨s₂, ?_, h.congr sb₂ (by rw [wr₂, wr₁]), by rw [k₂, k₁]; rfl, fun i hi => ?_, fun k hk1 hk2 hk3 => ?_,
      fun r h1 h2 h3 => by rw [g₂ r h1 h2 h3, g₁ r h1 h2 h3], by rw [rd₂, rd₁], by rw [wr₂, wr₁],
      f₁.trans (by unfold scratchR at f₂ ⊢; rw [sb₁] at f₂; exact f₂)⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_append, e₁, Option.bind_some, List.flatMap_singleton, e₂]
    · rcases (show i < 2 * n ∨ i = 2 * n ∨ i = 2 * n + 1 by omega) with hi' | rfl | rfl
      · rw [o₂ _ (uSlot_lt (by omega)) (by simp [uSlot]; omega) (by simp [uSlot]; omega)
          (.inl (by simp [uSlot, keySlot, aSlot, tailSlot]; omega)), v₁ i hi']
      · rw [a₂, k₁, gInput_even]
      · rw [b₂, k₁, gInput_odd]
    · rw [o₂ k hk1 (by simp [uSlot] at hk2 ⊢; omega) (by simp [uSlot] at hk2 ⊢; omega) hk3,
        o₁ k hk1 (by simp [uSlot] at hk2 ⊢; omega) hk3]

end VG.Proof.Seed.X86
