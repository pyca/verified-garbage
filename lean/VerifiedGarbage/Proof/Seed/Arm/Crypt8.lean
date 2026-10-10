import VerifiedGarbage.Proof.Seed.Arm.Round
import VerifiedGarbage.Proof.Seed.Rounds
import VerifiedGarbage.Proof.Seed.Memory

/-!
# Eight blocks of SEED on ARMv7

`crypt8_wp`: `crypt8` turns each of the eight blocks of the tail buffer into
`Spec.Seed.crypt` of it, with round `j + 1`'s key in the table's slots
`tableSlot + 2j` and `tableSlot + 2j + 1` (`tableKeys`). It copies the
blocks' words, byte-reversed, to the arrays (`toArr`, by `moves_ok`), runs
the eight pairs of rounds (`rounds_wp`), and copies the arrays back, `R`
first (`fromArr`).
-/

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
    have hpd : p.2 < slots := by omega
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
      · rw [o' _ (by have := (hL q List.mem_cons_self).2; omega) hnd.1, sl₁ _ hpd, ite_eq_left rfl]; rfl
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
      exact Straight.slot_contains _ hp.2 (by omega)

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
    have : arrSlot w + b < tailSlot := by simp [arrSlot, tailSlot]; omega
    omega

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
    have : tailAt b w < tableSlot := by simp [tailAt, tailSlot, tableSlot]; omega
    omega

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
    round_ok halves0 halves2 (by decide) h (k := k) (by rw [slots_eq]; omega) hkp
  have hkp₁ : KeyAt s₁ (k + 2) := by
    rw [KeyAt, kp₁, hkp, sb₁, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_ofNat]
    rfl
  obtain ⟨s₂, e₂, q₂, h₂, rd₂, wr₂, sp₂, kp₂, sb₂, sl₂, f₂⟩ :=
    round_ok halves2 halves0 (by decide) h₁ (k := k + 2) (by rw [slots_eq]; omega) hkp₁
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
    rw [e, q₂ b hb, q₁ b hb, sl₁ _ (by simp [tailSlot]; omega) (by rw [slots_eq]; omega),
      sl₁ _ (by simp [tailSlot]; omega) (by rw [slots_eq]; omega)]
  · rw [KeyAt, g₃ _ (by decide), hkp₂, sb₃]
  · rw [sl₃, sl₂ j hj1 hj2, sl₁ j hj1 hj2]
  · rw [m₃]; exact f₁.trans (by simpa [workR, sb₁] using f₂)
  · have e2 : s₂.gpr sb = s.gpr sb := by rw [sb₂, sb₁]
    rw [z₃, hkp₂, e2, Offset.add_sub_cancel_left, ofNat32_sub_beq (by omega) (by omega)]
    simp only [decide_eq_decide]; omega

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
    ⟨0, rfl, by omega, h.congr sb₁ wr₁, sb₁, by rw [KeyAt, k₁, sb₁]; rfl,
      fun b _ => by simp only [quadAt, lv, sl₁]; rfl, rd₁, wr₁, sp₁, fun j _ _ => sl₁ j,
      by rw [m₁]; exact Frame.refl _ _⟩
  obtain ⟨m, rfl, hm8, hR, hsb, hkp, hq, hrd, hwr, hsp, hsl, hf⟩ := hs
  obtain ⟨s', e', q', R', rd', wr', sp', kp', sb', sl', f', z'⟩ :=
    roundPair_ok hR (k := tableSlot + 4 * m) (by simp [tableEnd]; omega) (by omega) hkp
  have hkeys : ∀ i < 4, slotW s (tableSlot + 4 * m + i) = slotW s₀ (tableSlot + 4 * m + i) := fun i hi =>
    hsl _ (by simp [tailSlot, tableSlot]; omega) (by rw [slots_eq]; simp [tableSlot]; omega)
  have inv' : ∀ b < 8, quadAt s' (arrSlot 0) (arrSlot 2) b =
      roundsN (tableKeys s₀) (2 * (m + 1)) (quadAt s₀ (arrSlot 0) (arrSlot 2) b) := by
    intro b hb
    rw [q' b hb, hq b hb, show 2 * (m + 1) = 2 * m + 1 + 1 by omega, roundsN_succ, roundsN_succ,
      hkeys 2 (by omega), hkeys 3 (by omega), hkeys 1 (by omega),
      show tableSlot + 4 * m = tableSlot + 4 * m + 0 from rfl, hkeys 0 (by omega)]
    simp only [tableKeys]
    rw [show tableSlot + 2 * (2 * m) = tableSlot + 4 * m + 0 by omega,
      show tableSlot + 2 * (2 * m + 1) = tableSlot + 4 * m + 2 by omega,
      show tableSlot + 4 * m + 0 + 1 = tableSlot + 4 * m + 1 by omega,
      show tableSlot + 4 * m + 2 + 1 = tableSlot + 4 * m + 3 by omega]
  refine WP.of_runBlock ⟨s', e', ?_⟩
  have hf' : Frame [workR s₀] s₀.mem s'.mem := hf.trans (by simpa [workR, hsb] using f')
  have hsl' : ∀ j, tailSlot ≤ j → j < slots → slotW s' j = slotW s₀ j := fun j h1 h2 => by
    rw [sl' j h1 h2, hsl j h1 h2]
  by_cases h8 : m + 1 = 8
  · refine .inl ⟨by rw [eval_ne, z']; simp [tableEnd]; omega, fun b hb => ?_, R', by rw [rd', hrd],
      by rw [wr', hwr], by rw [sp', hsp], by rw [sb', hsb], hsl', hf'⟩
    rw [inv' b hb, h8]
  · refine .inr ⟨by rw [eval_ne, z']; simp [tableEnd]; omega, 8 - (m + 1), by omega, m + 1, rfl, by omega,
      R', by rw [sb', hsb], by rw [show tableSlot + 4 * (m + 1) = tableSlot + 4 * m + 4 by omega]; exact kp', inv', by rw [rd', hrd], by rw [wr', hwr], by rw [sp', hsp],
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
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [h4.1]; simp [hi]
  · rw [h4.2.1]; simp [hi]
  · rw [h4.2.2.1]; simp [hi]
  · rw [h4.2.2.2]; simp [hi]

/-- Word `w` of block `b` of the tail buffer, as a slot. -/
theorem tail_word {s : State} (h : Room s) {b w : Nat} (hb : b < 8) (hw : w < 4) :
    State.addr (s.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * b) + BitVec.ofNat 64 (4 * w) =
      slotA s (tailAt b w) := by
  have hf := h.fit; rw [slots_eq] at hf
  rw [slotA, slot_addr (by simp [tailAt, tailSlot]; omega), Offset.add_add]
  congr 2; simp [tailAt]; omega

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
    rw [o₁ _ (by rw [slots_eq]; simp [tableSlot]; omega) (by simp [tailSlot, tableSlot]; omega),
      o₁ _ (by rw [slots_eq]; simp [tableSlot]; omega) (by simp [tailSlot, tableSlot]; omega)]
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
        rw [BitVec.ofNat_add_ofNat]; congr 1; omega,
      ← BitVec.add_assoc, Mem.readW_byte s₃.mem _ (Nat.mod_lt i (by decide))]
    rw [← g₃ sb (by decide), tail_word h₃ hb (by omega), ← slotW, v₃ _ (by omega) b hb,
      byteRev32_byte _ (Nat.mod_lt _ (by decide))]
    congr 2
    simp only [quadAt]
    rcases (show i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3 by omega) with e | e | e | e <;>
      rw [e] <;> rfl
  · rw [o₃ j hj2 hj1, sl₂ j (by simp [tableSlot, tailSlot] at hj1 ⊢; omega) hj2,
      o₁ j hj2 (by simp [tableSlot, tailSlot] at hj1 ⊢; omega)]
  · refine (f₁.trans (by simpa [workR, sb₁] using f₂)).sub (fun r hr => ?_) |>.trans
      (by simpa [sb₂, sb₁] using f₃)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by simp [tailSlot, tableSlot])⟩

end VG.Proof.Seed.Arm
